//===-LTOBackend.cpp - LLVM Link Time Optimizer Backend -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the "backend" phase of LTO, i.e. it performs
// optimization and code generation on a loaded module. It is generally used
// internally by the LTO class but can also be used independently, for example
// to implement a standalone ThinLTO backend.
//
//===----------------------------------------------------------------------===//

#include "llvm/LTO/LTOBackend.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/ModuleSummaryAnalysis.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/LLVMRemarkStreamer.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/LTO/LTO.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Object/ModuleSymbolTable.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/IPO/ElimAvailExtern.h"
#include "llvm/Transforms/IPO/GlobalDCE.h"
#include "llvm/TargetParser/SubtargetFeature.h"
#include "llvm/Transforms/IPO/SampleProfile.h"
#include "llvm/Transforms/IPO/WholeProgramDevirt.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/FunctionImportUtils.h"
#include "llvm/Transforms/Utils/SplitModule.h"
#include "llvm/Transforms/Utils/SplitModuleCG.h"
#include <optional>

using namespace llvm;
using namespace lto;

#define DEBUG_TYPE "lto-backend"

enum class LTOBitcodeEmbedding {
  DoNotEmbed = 0,
  EmbedOptimized = 1,
  EmbedPostMergePreOptimized = 2
};

static cl::opt<LTOBitcodeEmbedding> EmbedBitcode(
    "lto-embed-bitcode", cl::init(LTOBitcodeEmbedding::DoNotEmbed),
    cl::values(clEnumValN(LTOBitcodeEmbedding::DoNotEmbed, "none",
                          "Do not embed"),
               clEnumValN(LTOBitcodeEmbedding::EmbedOptimized, "optimized",
                          "Embed after all optimization passes"),
               clEnumValN(LTOBitcodeEmbedding::EmbedPostMergePreOptimized,
                          "post-merge-pre-opt",
                          "Embed post merge, but before optimizations")),
    cl::desc("Embed LLVM bitcode in object files produced by LTO"));

static cl::opt<bool> ThinLTOAssumeMerged(
    "thinlto-assume-merged", cl::init(false),
    cl::desc("Assume the input has already undergone ThinLTO function "
             "importing and the other pre-optimization pipeline changes."));

static cl::opt<bool> splitOptAndCodeGen(
    "thinlto-split-optandcodegen", cl::init(true),
    cl::desc("enable split optandcodegen in thinlto backend."));
static cl::opt<bool> ThinLTOCombineOutput(
    "thinlto-split-combine-output", cl::init(true),
    cl::desc("combine the split output to a .o in thinlto backend."));
static cl::opt<bool>
    ThinLTOUseCG("thinlto-use-callgraph", cl::init(true),
                 cl::desc("use callgraph to split module in thinlto backend."));
static cl::opt<unsigned> ThinLTOSplitThreshold(
    "thinlto-split-threshold", cl::Hidden, cl::init(2),
    cl::desc("control the amount of whether split in thinlto backend."));
static cl::opt<unsigned> ThinLTOSplitModuleSizeThreshold(
    "thinlto-split-module-size-threshold", cl::Hidden, cl::init(500),
    cl::desc("Control the amount of whether split in thinlto backend"
"accroding to the size of a module."));
static cl::opt<unsigned> ThinLTOSplitPartitions(
    "thinlto-split-partitions", cl::Hidden, cl::init(0),
    cl::desc("control split to how many partitions in thinlto backend."));
static cl::opt<bool>
    ThinLTODebugMpart("thinlto-debug-mpart", cl::init(false),
                      cl::desc("debug mpart when split module."));

namespace llvm {
extern cl::opt<bool> NoPGOWarnMismatch;
extern cl::opt<bool> ThinLTOSplit;
}

[[noreturn]] static void reportOpenError(StringRef Path, Twine Msg) {
  errs() << "failed to open " << Path << ": " << Msg << '\n';
  errs().flush();
  exit(1);
}

Error Config::addSaveTemps(std::string OutputFileName, bool UseInputModulePath,
                           const DenseSet<StringRef> &SaveTempsArgs) {
  ShouldDiscardValueNames = false;

  std::error_code EC;
  if (SaveTempsArgs.empty() || SaveTempsArgs.contains("resolution")) {
    ResolutionFile =
        std::make_unique<raw_fd_ostream>(OutputFileName + "resolution.txt", EC,
                                         sys::fs::OpenFlags::OF_TextWithCRLF);
    if (EC) {
      ResolutionFile.reset();
      return errorCodeToError(EC);
    }
  }

  auto setHook = [&](std::string PathSuffix, ModuleHookFn &Hook) {
    // Keep track of the hook provided by the linker, which also needs to run.
    ModuleHookFn LinkerHook = Hook;
    Hook = [=](unsigned Task, const Module &M) {
      // If the linker's hook returned false, we need to pass that result
      // through.
      if (LinkerHook && !LinkerHook(Task, M))
        return false;

      auto extract_filename = [](const std::string &path) -> std::string {
        return llvm::sys::path::filename(path).str();
      };

      std::string PathPrefix;
      // If this is the combined module (not a ThinLTO backend compile) or the
      // user hasn't requested using the input module's path, emit to a file
      // named from the provided OutputFileName with the Task ID appended.
      if (M.getModuleIdentifier() == "ld-temp.o" || !UseInputModulePath) {
        PathPrefix = OutputFileName;
        if (ThinLTOSplit)
          PathPrefix += extract_filename(M.getSourceFileName()) + ".";
        if (Task != (unsigned)-1)
          PathPrefix += utostr(Task) + ".";
      } else
        PathPrefix = M.getModuleIdentifier() + ".";
      std::string Path = PathPrefix + PathSuffix + ".bc";
      std::error_code EC;
      raw_fd_ostream OS(Path, EC, sys::fs::OpenFlags::OF_None);
      // Because -save-temps is a debugging feature, we report the error
      // directly and exit.
      if (EC)
        reportOpenError(Path, EC.message());
      WriteBitcodeToFile(M, OS, /*ShouldPreserveUseListOrder=*/false);
      return true;
    };
  };

  auto SaveCombinedIndex =
      [=](const ModuleSummaryIndex &Index,
          const DenseSet<GlobalValue::GUID> &GUIDPreservedSymbols) {
        std::string Path = OutputFileName + "index.bc";
        std::error_code EC;
        raw_fd_ostream OS(Path, EC, sys::fs::OpenFlags::OF_None);
        // Because -save-temps is a debugging feature, we report the error
        // directly and exit.
        if (EC)
          reportOpenError(Path, EC.message());
        writeIndexToFile(Index, OS);

        Path = OutputFileName + "index.dot";
        raw_fd_ostream OSDot(Path, EC, sys::fs::OpenFlags::OF_None);
        if (EC)
          reportOpenError(Path, EC.message());
        Index.exportToDot(OSDot, GUIDPreservedSymbols);
        return true;
      };

  if (SaveTempsArgs.empty()) {
    setHook("0.preopt", PreOptModuleHook);
    setHook("1.promote", PostPromoteModuleHook);
    setHook("2.internalize", PostInternalizeModuleHook);
    setHook("3.import", PostImportModuleHook);
    setHook("4.opt", PostOptModuleHook);
    setHook("5.precodegen", PreCodeGenModuleHook);
    CombinedIndexHook = SaveCombinedIndex;
  } else {
    if (SaveTempsArgs.contains("preopt"))
      setHook("0.preopt", PreOptModuleHook);
    if (SaveTempsArgs.contains("promote"))
      setHook("1.promote", PostPromoteModuleHook);
    if (SaveTempsArgs.contains("internalize"))
      setHook("2.internalize", PostInternalizeModuleHook);
    if (SaveTempsArgs.contains("import"))
      setHook("3.import", PostImportModuleHook);
    if (SaveTempsArgs.contains("opt"))
      setHook("4.opt", PostOptModuleHook);
    if (SaveTempsArgs.contains("precodegen"))
      setHook("5.precodegen", PreCodeGenModuleHook);
    if (SaveTempsArgs.contains("combinedindex"))
      CombinedIndexHook = SaveCombinedIndex;
  }

  return Error::success();
}

#define HANDLE_EXTENSION(Ext)                                                  \
  llvm::PassPluginLibraryInfo get##Ext##PluginInfo();
#include "llvm/Support/Extension.def"

static void RegisterPassPlugins(ArrayRef<std::string> PassPlugins,
                                PassBuilder &PB) {
#define HANDLE_EXTENSION(Ext)                                                  \
  get##Ext##PluginInfo().RegisterPassBuilderCallbacks(PB);
#include "llvm/Support/Extension.def"

  // Load requested pass plugins and let them register pass builder callbacks
  for (auto &PluginFN : PassPlugins) {
    auto PassPlugin = PassPlugin::Load(PluginFN);
    if (!PassPlugin) {
      errs() << "Failed to load passes from '" << PluginFN
             << "'. Request ignored.\n";
      continue;
    }

    PassPlugin->registerPassBuilderCallbacks(PB);
  }
}

static std::unique_ptr<TargetMachine>
createTargetMachine(const Config &Conf, const Target *TheTarget, Module &M) {
  StringRef TheTriple = M.getTargetTriple();
  SubtargetFeatures Features;
  Features.getDefaultSubtargetFeatures(Triple(TheTriple));
  for (const std::string &A : Conf.MAttrs)
    Features.AddFeature(A);

  std::optional<Reloc::Model> RelocModel;
  if (Conf.RelocModel)
    RelocModel = *Conf.RelocModel;
  else if (M.getModuleFlag("PIC Level"))
    RelocModel =
        M.getPICLevel() == PICLevel::NotPIC ? Reloc::Static : Reloc::PIC_;

  std::optional<CodeModel::Model> CodeModel;
  if (Conf.CodeModel)
    CodeModel = *Conf.CodeModel;
  else
    CodeModel = M.getCodeModel();

  std::unique_ptr<TargetMachine> TM(TheTarget->createTargetMachine(
      TheTriple, Conf.CPU, Features.getString(), Conf.Options, RelocModel,
      CodeModel, Conf.CGOptLevel));
  assert(TM && "Failed to create target machine");
  return TM;
}

static void runProfileLoaderPass(const Config &Conf, Module &Mod,
                                 TargetMachine *TM) {
  auto FS = vfs::getRealFileSystem();
  std::optional<PGOOptions> PGOOpt;
  if (!Conf.SampleProfile.empty())
    PGOOpt = PGOOptions(Conf.SampleProfile, "", Conf.ProfileRemapping,
                        /*MemoryProfile=*/"", FS, PGOOptions::SampleUse,
                        PGOOptions::NoCSAction, true);
  else if (Conf.RunCSIRInstr) {
    PGOOpt = PGOOptions("", Conf.CSIRProfile, Conf.ProfileRemapping,
                        /*MemoryProfile=*/"", FS, PGOOptions::IRUse,
                        PGOOptions::CSIRInstr, Conf.AddFSDiscriminator);
  } else if (!Conf.CSIRProfile.empty()) {
    PGOOpt = PGOOptions(Conf.CSIRProfile, "", Conf.ProfileRemapping,
                        /*MemoryProfile=*/"", FS, PGOOptions::IRUse,
                        PGOOptions::CSIRUse, Conf.AddFSDiscriminator);
    NoPGOWarnMismatch = !Conf.PGOWarnMismatch;
  } else if (Conf.AddFSDiscriminator) {
    PGOOpt = PGOOptions("", "", "", /*MemoryProfile=*/"", nullptr,
                        PGOOptions::NoAction, PGOOptions::NoCSAction, true);
  }
  bool HasSampleProfile = PGOOpt && (PGOOpt->Action == PGOOptions::SampleUse);
  if (!HasSampleProfile)
    return;

  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;
  PassInstrumentationCallbacks PIC;

  PassBuilder PB(TM, Conf.PTO, PGOOpt, &PIC);

  RegisterPassPlugins(Conf.PassPlugins, PB);

  // Register all the basic analyses with the managers.
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  ModulePassManager MPM;
  MPM.addPass(SampleProfileLoaderPass(PGOOpt->ProfileFile,
                                      PGOOpt->ProfileRemappingFile,
                                      ThinOrFullLTOPhase::ThinLTOPostLink));
  MPM.addPass(RequireAnalysisPass<ProfileSummaryAnalysis, Module>());
  MPM.run(Mod, MAM);
}

static void runGlobalDCEPass(Module &Mod) {
  ModuleAnalysisManager MAM;
  PassBuilder PB;
  PB.registerModuleAnalyses(MAM);

  ModulePassManager MPM;
  MPM.addPass(EliminateAvailableExternallyPass());
  MPM.addPass(GlobalDCEPass());
  MPM.run(Mod, MAM);
}

static void runNewPMPasses(const Config &Conf, Module &Mod, TargetMachine *TM,
                           unsigned OptLevel, bool IsThinLTO,
                           ModuleSummaryIndex *ExportSummary,
                           const ModuleSummaryIndex *ImportSummary) {
  auto FS = vfs::getRealFileSystem();
  std::optional<PGOOptions> PGOOpt;
  if (!Conf.SampleProfile.empty())
    PGOOpt = PGOOptions(Conf.SampleProfile, "", Conf.ProfileRemapping,
                        /*MemoryProfile=*/"", FS, PGOOptions::SampleUse,
                        PGOOptions::NoCSAction, true);
  else if (Conf.RunCSIRInstr) {
    PGOOpt = PGOOptions("", Conf.CSIRProfile, Conf.ProfileRemapping,
                        /*MemoryProfile=*/"", FS, PGOOptions::IRUse,
                        PGOOptions::CSIRInstr, Conf.AddFSDiscriminator);
  } else if (!Conf.CSIRProfile.empty()) {
    PGOOpt = PGOOptions(Conf.CSIRProfile, "", Conf.ProfileRemapping,
                        /*MemoryProfile=*/"", FS, PGOOptions::IRUse,
                        PGOOptions::CSIRUse, Conf.AddFSDiscriminator);
    NoPGOWarnMismatch = !Conf.PGOWarnMismatch;
  } else if (Conf.AddFSDiscriminator) {
    PGOOpt = PGOOptions("", "", "", /*MemoryProfile=*/"", nullptr,
                        PGOOptions::NoAction, PGOOptions::NoCSAction, true);
  }
  TM->setPGOOption(PGOOpt);

  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  PassInstrumentationCallbacks PIC;
  StandardInstrumentations SI(Mod.getContext(), Conf.DebugPassManager,
                              Conf.VerifyEach);
  SI.registerCallbacks(PIC, &MAM);
  PassBuilder PB(TM, Conf.PTO, PGOOpt, &PIC);

  RegisterPassPlugins(Conf.PassPlugins, PB);

  std::unique_ptr<TargetLibraryInfoImpl> TLII(
      new TargetLibraryInfoImpl(Triple(TM->getTargetTriple())));
  if (Conf.Freestanding)
    TLII->disableAllFunctions();
  FAM.registerPass([&] { return TargetLibraryAnalysis(*TLII); });

  // Parse a custom AA pipeline if asked to.
  if (!Conf.AAPipeline.empty()) {
    AAManager AA;
    if (auto Err = PB.parseAAPipeline(AA, Conf.AAPipeline)) {
      report_fatal_error(Twine("unable to parse AA pipeline description '") +
                         Conf.AAPipeline + "': " + toString(std::move(Err)));
    }
    // Register the AA manager first so that our version is the one used.
    FAM.registerPass([&] { return std::move(AA); });
  }

  // Register all the basic analyses with the managers.
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  ModulePassManager MPM;

  if (!Conf.DisableVerify)
    MPM.addPass(VerifierPass());

  OptimizationLevel OL;

  switch (OptLevel) {
  default:
    llvm_unreachable("Invalid optimization level");
  case 0:
    OL = OptimizationLevel::O0;
    break;
  case 1:
    OL = OptimizationLevel::O1;
    break;
  case 2:
    OL = OptimizationLevel::O2;
    break;
  case 3:
    OL = OptimizationLevel::O3;
    break;
  }

  // Parse a custom pipeline if asked to.
  if (!Conf.OptPipeline.empty()) {
    if (auto Err = PB.parsePassPipeline(MPM, Conf.OptPipeline)) {
      report_fatal_error(Twine("unable to parse pass pipeline description '") +
                         Conf.OptPipeline + "': " + toString(std::move(Err)));
    }
  } else if (Conf.UseDefaultPipeline) {
    MPM.addPass(PB.buildPerModuleDefaultPipeline(OL));
  } else if (IsThinLTO) {
    MPM.addPass(PB.buildThinLTODefaultPipeline(OL, ImportSummary));
  } else {
    MPM.addPass(PB.buildLTODefaultPipeline(OL, ExportSummary));
  }

  if (!Conf.DisableVerify)
    MPM.addPass(VerifierPass());

  MPM.run(Mod, MAM);
}

bool lto::opt(const Config &Conf, TargetMachine *TM, unsigned Task, Module &Mod,
              bool IsThinLTO, ModuleSummaryIndex *ExportSummary,
              const ModuleSummaryIndex *ImportSummary,
              const std::vector<uint8_t> &CmdArgs) {
  if (EmbedBitcode == LTOBitcodeEmbedding::EmbedPostMergePreOptimized) {
    // FIXME: the motivation for capturing post-merge bitcode and command line
    // is replicating the compilation environment from bitcode, without needing
    // to understand the dependencies (the functions to be imported). This
    // assumes a clang - based invocation, case in which we have the command
    // line.
    // It's not very clear how the above motivation would map in the
    // linker-based case, so we currently don't plumb the command line args in
    // that case.
    if (CmdArgs.empty())
      LLVM_DEBUG(
          dbgs() << "Post-(Thin)LTO merge bitcode embedding was requested, but "
                    "command line arguments are not available");
    llvm::embedBitcodeInModule(Mod, llvm::MemoryBufferRef(),
                               /*EmbedBitcode*/ true, /*EmbedCmdline*/ true,
                               /*Cmdline*/ CmdArgs);
  }
  // FIXME: Plumb the combined index into the new pass manager.
  runNewPMPasses(Conf, Mod, TM, Conf.OptLevel, IsThinLTO, ExportSummary,
                 ImportSummary);
  return !Conf.PostOptModuleHook || Conf.PostOptModuleHook(Task, Mod);
}

static void codegen(const Config &Conf, TargetMachine *TM,
                    AddStreamFn AddStream, unsigned Task, Module &Mod,
                    const ModuleSummaryIndex &CombinedIndex) {
  if (Conf.PreCodeGenModuleHook && !Conf.PreCodeGenModuleHook(Task, Mod))
    return;

  if (EmbedBitcode == LTOBitcodeEmbedding::EmbedOptimized)
    llvm::embedBitcodeInModule(Mod, llvm::MemoryBufferRef(),
                               /*EmbedBitcode*/ true,
                               /*EmbedCmdline*/ false,
                               /*CmdArgs*/ std::vector<uint8_t>());

  std::unique_ptr<ToolOutputFile> DwoOut;
  SmallString<1024> DwoFile(Conf.SplitDwarfOutput);
  if (!Conf.DwoDir.empty()) {
    std::error_code EC;
    if (auto EC = llvm::sys::fs::create_directories(Conf.DwoDir))
      report_fatal_error(Twine("Failed to create directory ") + Conf.DwoDir +
                         ": " + EC.message());

    DwoFile = Conf.DwoDir;
    sys::path::append(DwoFile, std::to_string(Task) + ".dwo");
    TM->Options.MCOptions.SplitDwarfFile = std::string(DwoFile);
  } else {
    // Keep original behavior for sentinel task id (-1 casted to unsigned).
    // In this mode the output path is fixed (Conf.SplitDwarfOutput).
    if (Task == std::numeric_limits<unsigned>::max()) {
      TM->Options.MCOptions.SplitDwarfFile = Conf.SplitDwarfFile;
    } else if (!DwoFile.empty()) {
      // Derive a unique filename by injecting ".<Task>" before extension.
      llvm::StringRef Dir = sys::path::parent_path(DwoFile);
      llvm::StringRef Stem = sys::path::stem(DwoFile);
      llvm::StringRef Ext = sys::path::extension(DwoFile); // usually ".dwo"

      llvm::SmallString<1024> UniquePath;
      if (!Dir.empty()) {
        UniquePath = Dir;
        sys::path::append(UniquePath, "");
      }

      llvm::SmallString<256> Name;
      Name += Stem;
      Name += ".";
      Name += llvm::utostr(Task);
      Name += Ext.empty() ? ".dwo" : Ext;

      if (!Dir.empty())
        sys::path::append(UniquePath, Name);
      else
        UniquePath = Name;

      DwoFile = UniquePath;
      TM->Options.MCOptions.SplitDwarfFile = std::string(DwoFile);
    } else {
      TM->Options.MCOptions.SplitDwarfFile = Conf.SplitDwarfFile;
    }
  }
  if (!DwoFile.empty()) {
    std::error_code EC;
    DwoOut = std::make_unique<ToolOutputFile>(DwoFile, EC, sys::fs::OF_None);
    if (EC)
      report_fatal_error(Twine("Failed to open ") + DwoFile + ": " +
                         EC.message());
  }

  Expected<std::unique_ptr<CachedFileStream>> StreamOrErr =
      AddStream(Task, Mod.getModuleIdentifier());
  if (Error Err = StreamOrErr.takeError())
    report_fatal_error(std::move(Err));
  std::unique_ptr<CachedFileStream> &Stream = *StreamOrErr;
  TM->Options.ObjectFilenameForDebug = Stream->ObjectPathName;

  legacy::PassManager CodeGenPasses;
  TargetLibraryInfoImpl TLII(Triple(Mod.getTargetTriple()));
  CodeGenPasses.add(new TargetLibraryInfoWrapperPass(TLII));
  CodeGenPasses.add(
      createImmutableModuleSummaryIndexWrapperPass(&CombinedIndex));
  if (Conf.PreCodeGenPassesHook)
    Conf.PreCodeGenPassesHook(CodeGenPasses);
  if (TM->addPassesToEmitFile(CodeGenPasses, *Stream->OS,
                              DwoOut ? &DwoOut->os() : nullptr,
                              Conf.CGFileType))
    report_fatal_error("Failed to setup codegen");
  CodeGenPasses.run(Mod);

  if (DwoOut)
    DwoOut->keep();
}

static void splitCodeGenThin(
    unsigned task, const Config &C, TargetMachine *TM, AddStreamFn AddStream,
    unsigned ParallelCodeGenParallelismLevel, Module &Mod,
    const ModuleSummaryIndex &CombinedIndex, ThreadPool *PartitionThreadPool,
    std::vector<std::vector<SmallString<0>>> &bufPart) {
  unsigned ThreadCount = 0;
  const Target *T = &TM->getTarget();

  SplitModuleCG SplitModuleCG(Mod, C, ParallelCodeGenParallelismLevel);
  if (ThinLTOUseCG)
    ParallelCodeGenParallelismLevel = SplitModuleCG.getPartitionNum();

  bufPart[task].resize(ParallelCodeGenParallelismLevel);

  const auto HandleModulePartition = [&](std::unique_ptr<Module> MPart) {
    // We want to clone the module in a new context to multi-thread the
    // codegen. We do it by serializing partition modules to bitcode
    // (while still on the main thread, in order to avoid data races) and
    // spinning up new threads which deserialize the partitions into
    // separate contexts.
    // FIXME: Provide a more direct way to do this in LLVM.
    SmallString<0> BC;
    raw_svector_ostream BCOS(BC);
    WriteBitcodeToFile(*MPart, BCOS);

    // Enqueue the task
    PartitionThreadPool->async(
        [&](const SmallString<0> &BC, unsigned ThreadId) {
          LTOLLVMContext Ctx(C);
          Expected<std::unique_ptr<Module>> MOrErr =
              parseBitcodeFile(MemoryBufferRef(BC.str(), "ld-temp.o"), Ctx);
          if (!MOrErr)
            report_fatal_error("Failed to read bitcode");
          std::unique_ptr<Module> MPartInCtx = std::move(MOrErr.get());

          std::unique_ptr<TargetMachine> TM =
              createTargetMachine(C, T, *MPartInCtx);

          AddStreamFn splitStream = [&](size_t task, const Twine &moduleName) {
            return std::make_unique<CachedFileStream>(
                std::make_unique<raw_svector_ostream>(bufPart[task][ThreadId]));
          };

          codegen(C, TM.get(), splitStream, task, *MPartInCtx, CombinedIndex);
        },
        // Pass BC using std::move to ensure that it get moved rather than
        // copied into the thread's context.
        std::move(BC), ThreadCount++);
  };

  if (ThinLTOUseCG)
    SplitModuleCG.SplitModule(TM, HandleModulePartition, false);
  else
    SplitModule(Mod, ParallelCodeGenParallelismLevel, HandleModulePartition,
                false);

  // Because the inner lambda (which runs in a worker thread) captures our local
  // variables, we need to wait for the worker threads to terminate before we
  // can leave the function scope.
  PartitionThreadPool->wait();
}

static unsigned countDefinedFunctions(const llvm::Module &M) {
  unsigned Count = 0;
  for (const auto &F : M)
    if (!F.isDeclaration())
      Count++;
  return Count;
}

static unsigned calModuleSize(const llvm::Module &M) {
  unsigned size = 0;
  for (const auto &F : M)
    for (const auto &BB : F)
      size += std::distance(BB.begin(), BB.end());
  return size;
}

static bool canDoSplitModule(const llvm::Module &M) {
  if (calModuleSize(M) < ThinLTOSplitModuleSizeThreshold)
    return false;
  if (countDefinedFunctions(M) < ThinLTOSplitThreshold)
    return false;
  return true;
}

using Clock = std::chrono::high_resolution_clock;
using Ms = std::chrono::milliseconds;
struct TaskIdAllocator {
  using TaskId = unsigned;

  // Use the most significant bit (MSB) as a namespace tag.
  // - Original ThinLTO backend tasks are expected to have MSB == 0.
  // - Split partitions allocated by this allocator always have MSB == 1.
  // This guarantees the two ID spaces never overlap.
  static constexpr TaskId tag() {
    return TaskId{1} << (std::numeric_limits<TaskId>::digits - 1);
  }

  // Monotonic sequence counter for split partitions (MSB must remain 0 here).
  std::atomic<TaskId> seq{0};

  // Allocate a globally unique TaskId for a split partition.
  // The returned ID is `tag() | seq`, so it lives in the MSB==1 namespace.
  TaskId alloc() {
    TaskId v = seq.fetch_add(1, std::memory_order_relaxed);

    // If the counter ever reaches the MSB, we'd overlap namespaces.
    // This indicates an overflow / too many partitions.
    if (v & tag())
      report_fatal_error("Partition TaskId overflow: seq reached the tag bit.");

    return tag() | v;
  }

  // Helper for sanity checks / debugging.
  static bool isPartition(TaskId id) { return (id & tag()) != 0; }
};

// Global allocator shared by all split partitions.
static TaskIdAllocator gSplitTaskIds;

static bool splitOptAndCodeGenThin(unsigned task, const Config &C,
                                   TargetMachine *TM, AddStreamFn AddStream,
                                   unsigned ParallelCodeGenParallelismLevel,
                                   Module &Mod,
                                   const ModuleSummaryIndex &CombinedIndex,
                                   const std::vector<uint8_t> &CmdArgs,
                                   ThreadPool *PartitionThreadPool,
                                   bool DoOpt) {
  unsigned ThreadCount = 0;
  const Target *T = &TM->getTarget();

  // [Timing] 1.start
  auto TimeStart = Clock::now();
  std::atomic<long> TotalOptTime{0};
  std::atomic<long> TotalCodeGenTime{0};
  static std::mutex PrintMutex;
  auto Mname = Mod.getModuleIdentifier();

  SplitModuleCG SplitModuleCG(Mod, C, ParallelCodeGenParallelismLevel,
                              PartitionThreadPool);
  if (ThinLTOUseCG)
    ParallelCodeGenParallelismLevel = SplitModuleCG.getPartitionNum();

  std::vector<std::string> TempObjectFiles(ParallelCodeGenParallelismLevel);

  if (ThinLTODebugMpart) {
    std::lock_guard<std::mutex> Lock(PrintMutex);
    LLVM_DEBUG(dbgs() << "before split, " << Mname << " \n");
    LLVM_DEBUG(Mod.dump());
  }

  const auto HandleModulePartition = [&](std::unique_ptr<Module> MPart) {
    // We want to clone the module in a new context to multi-thread the
    // codegen. We do it by serializing partition modules to bitcode
    // (while still on the main thread, in order to avoid data races) and
    // spinning up new threads which deserialize the partitions into
    // separate contexts.
    // FIXME: Provide a more direct way to do this in LLVM.
    // SmallString<0> BC;
    // raw_svector_ostream BCOS(BC);
    // WriteBitcodeToFile(*MPart, BCOS);

    if (ThinLTODebugMpart) {
      std::lock_guard<std::mutex> Lock(PrintMutex);
      LLVM_DEBUG(dbgs() << "before opt, MPart " << Mname << " \n");
      LLVM_DEBUG(MPart->dump());
    }

    unsigned CurrentThreadId, UniqueTaskId;
    {
      std::lock_guard<std::mutex> Lock(PrintMutex);
      CurrentThreadId = ThreadCount++;

      // In distributed ThinLTO, `task` may be a sentinel (e.g. -1 cast to
      // unsigned), which becomes UINT_MAX and naturally has MSB==1. Treat it
      // as "no base task id" and don't enforce the namespace check on it.
      //
      // We do not rely on the incoming `task` for partition uniqueness: split
      // partitions get a dedicated UniqueTaskId allocated below.
      if (task != std::numeric_limits<unsigned>::max()) {
        assert(!TaskIdAllocator::isPartition(task) &&
               "Original ThinLTO TaskId unexpectedly overlaps the partition "
               "namespace");
      }
      UniqueTaskId = gSplitTaskIds.alloc();
    }

    std::unique_ptr<TargetMachine> ThreadTM = createTargetMachine(C, T, *MPart);

    if (DoOpt) {
      auto StartOpt = Clock::now();
      if (!opt(C, ThreadTM.get(), UniqueTaskId, *MPart, /*IsThinLTO=*/true,
               /*ExportSummary=*/nullptr, /*ImportSummary=*/&CombinedIndex,
               CmdArgs)) {
        report_fatal_error("Failed to gen opt for split mod in thread.");
      }
      auto EndOpt = Clock::now();
      if (ThinLTODebugMpart) {
        {
          std::lock_guard<std::mutex> Lock(PrintMutex);
          LLVM_DEBUG(
              dbgs()
              << Mname << " Mpart " << CurrentThreadId << " opt cost: "
              << std::chrono::duration_cast<Ms>(EndOpt - StartOpt).count()
              << " ms\n");
        }
        TotalOptTime +=
            std::chrono::duration_cast<Ms>(EndOpt - StartOpt).count();
      }
    }

    auto PromotedRenames = SplitModuleCG.getPromotedRenames();
    for (auto &GV : MPart->global_values()) {
      if (auto It = PromotedRenames.find(GV.getName());
          It != PromotedRenames.end()) {
        GV.setName(It->second);
      }
    }
    if (ThinLTODebugMpart) {
      std::lock_guard<std::mutex> Lock(PrintMutex);
      LLVM_DEBUG(dbgs() << "after rename, MPart " << Mname << "\n");
      LLVM_DEBUG(MPart->dump());
    }

    auto splitStream = [&](unsigned task, const Twine &moduleName)
        -> Expected<std::unique_ptr<CachedFileStream>> {
      int FD;
      SmallString<128> TempFilename;
      if (std::error_code EC = sys::fs::createUniqueFile(
              "/dev/shm/thinlto-split-%%%%%%.o", FD, TempFilename))
        return errorCodeToError(EC);

      TempObjectFiles[CurrentThreadId] = std::string(TempFilename.str());

      auto OS =
          std::make_unique<raw_fd_ostream>(FD, true, /*CloseOnDestruct*/ true);

      auto Stream = std::make_unique<CachedFileStream>(
          std::move(OS), std::string(TempFilename.str()));

      return std::move(Stream);
    };

    auto StartCG = Clock::now();
    codegen(C, ThreadTM.get(), splitStream, UniqueTaskId, *MPart,
            CombinedIndex);
    auto EndCG = Clock::now();
    if (ThinLTODebugMpart) {
      {
        std::lock_guard<std::mutex> Lock(PrintMutex);
        LLVM_DEBUG(
            dbgs() << Mname << " Mpart " << CurrentThreadId << " codegen cost: "
                   << std::chrono::duration_cast<Ms>(EndCG - StartCG).count()
                   << " ms\n");
      }
      TotalCodeGenTime +=
          std::chrono::duration_cast<Ms>(EndCG - StartCG).count();
    }
    // },
    // Pass BC using std::move to ensure that it get moved rather than
    // copied into the thread's context.
    // std::move(BC));
  };

  if (ThinLTOUseCG)
    SplitModuleCG.SplitModule(TM, HandleModulePartition, false);
  else
    SplitModule(Mod, ParallelCodeGenParallelismLevel, HandleModulePartition,
                false);

  // Because the inner lambda (which runs in a worker thread) captures our local
  // variables, we need to wait for the worker threads to terminate before we
  // can leave the function scope.
  PartitionThreadPool->wait();

  if (TempObjectFiles.empty()) {
    llvm::errs() << "TempObjectFiles.empty()\n";
    return true;
  }

  // [Timing] 2. split + codegen time
  auto TimeAfterCodeGen = Clock::now();

  auto FinalStream = AddStream(task, Mod.getModuleIdentifier());
  if (!FinalStream)
    report_fatal_error("Failed to open final output stream");

  int MergedFD;
  SmallString<128> MergedFilename;
  if (sys::fs::createUniqueFile("/dev/shm/thinlto-merged-%%%%%%.o", MergedFD,
                                MergedFilename))
    report_fatal_error("Failed to create merged temp file.");
  sys::fs::file_t MergedNativeFD = sys::fs::convertFDToNativeFile(MergedFD);
  sys::fs::closeFile(MergedNativeFD);

  std::vector<StringRef> Args;
  std::string LinkerPath = "";
  if (auto Path = sys::findProgramByName("ld.lld"))
    LinkerPath = *Path;
  else if (auto Path = sys::findProgramByName("ld"))
    LinkerPath = *Path;

  if (LinkerPath.empty())
    report_fatal_error(
        "Cannot find linkeer (ld or ld.lld) to merge partitions.");

  Args.push_back(LinkerPath);
  Args.push_back("-r");
  Args.push_back("-o");
  Args.push_back(MergedFilename);

  for (const auto &File : TempObjectFiles)
    Args.push_back(File);

  std::string ErrMsg;
  int Result = sys::ExecuteAndWait(LinkerPath, Args, /*Env=*/std::nullopt,
                                   /*Redirects=*/{}, /*SecondsToWait=*/0,
                                   /*MemoryLimit=*/0, &ErrMsg);

  if (Result != 0) {
    errs() << "Linker failed: " << ErrMsg << "\n";
    report_fatal_error("Failed to merge split objects.");
  }

  {
    std::unique_ptr<CachedFileStream> &FinalFileStream = *FinalStream;
    auto BufferOrErr = MemoryBuffer::getFile(MergedFilename);
    if (!BufferOrErr)
      report_fatal_error("Failed to read merged object.");

    FinalFileStream->OS->write(BufferOrErr.get()->getBufferStart(),
                               BufferOrErr.get()->getBufferSize());
  }

  for (const auto &File : TempObjectFiles)
    sys::fs::remove(File);
  sys::fs::remove(MergedFilename);

  if (ThinLTODebugMpart) {
    // [Timing] 3. Link time
    auto TimeAfterLink = Clock::now();

    // [Timing] 4. calculate and print
    auto DurSplitCodegen =
        std::chrono::duration_cast<Ms>(TimeAfterCodeGen - TimeStart).count();
    auto DurLinking =
        std::chrono::duration_cast<Ms>(TimeAfterLink - TimeAfterCodeGen)
            .count();
    auto DurTotal =
        std::chrono::duration_cast<Ms>(TimeAfterLink - TimeStart).count();

    LLVM_DEBUG(dbgs() << Mname << "    Split & CodeGen   : " << DurSplitCodegen
                      << " ms\n");
    LLVM_DEBUG(dbgs() << Mname << "    Sum(Opt CPU Time) : "
                      << TotalOptTime.load() << " ms\n");
    LLVM_DEBUG(dbgs() << Mname << "    Sum(CG CPU Time)  : "
                      << TotalCodeGenTime.load() << " ms\n");
    LLVM_DEBUG(dbgs() << Mname << "    Link(ld -r)       : " << DurLinking
                      << " ms\n");
    LLVM_DEBUG(dbgs() << Mname << "    Total             : " << DurTotal
                      << " ms\n");
  }

  return true;
}


static void splitCodeGen(const Config &C, TargetMachine *TM,
                         AddStreamFn AddStream,
                         unsigned ParallelCodeGenParallelismLevel, Module &Mod,
                         const ModuleSummaryIndex &CombinedIndex) {
  ThreadPool CodegenThreadPool(
      heavyweight_hardware_concurrency(ParallelCodeGenParallelismLevel));
  unsigned ThreadCount = 0;
  const Target *T = &TM->getTarget();

  SplitModule(
      Mod, ParallelCodeGenParallelismLevel,
      [&](std::unique_ptr<Module> MPart) {
        // We want to clone the module in a new context to multi-thread the
        // codegen. We do it by serializing partition modules to bitcode
        // (while still on the main thread, in order to avoid data races) and
        // spinning up new threads which deserialize the partitions into
        // separate contexts.
        // FIXME: Provide a more direct way to do this in LLVM.
        SmallString<0> BC;
        raw_svector_ostream BCOS(BC);
        WriteBitcodeToFile(*MPart, BCOS);

        // Enqueue the task
        CodegenThreadPool.async(
            [&](const SmallString<0> &BC, unsigned ThreadId) {
              LTOLLVMContext Ctx(C);
              Expected<std::unique_ptr<Module>> MOrErr = parseBitcodeFile(
                  MemoryBufferRef(StringRef(BC.data(), BC.size()), "ld-temp.o"),
                  Ctx);
              if (!MOrErr)
                report_fatal_error("Failed to read bitcode");
              std::unique_ptr<Module> MPartInCtx = std::move(MOrErr.get());

              std::unique_ptr<TargetMachine> TM =
                  createTargetMachine(C, T, *MPartInCtx);

              codegen(C, TM.get(), AddStream, ThreadId, *MPartInCtx,
                      CombinedIndex);
            },
            // Pass BC using std::move to ensure that it get moved rather than
            // copied into the thread's context.
            std::move(BC), ThreadCount++);
      },
      false);

  // Because the inner lambda (which runs in a worker thread) captures our local
  // variables, we need to wait for the worker threads to terminate before we
  // can leave the function scope.
  CodegenThreadPool.wait();
}

static Expected<const Target *> initAndLookupTarget(const Config &C,
                                                    Module &Mod) {
  if (!C.OverrideTriple.empty())
    Mod.setTargetTriple(C.OverrideTriple);
  else if (Mod.getTargetTriple().empty())
    Mod.setTargetTriple(C.DefaultTriple);

  std::string Msg;
  const Target *T = TargetRegistry::lookupTarget(Mod.getTargetTriple(), Msg);
  if (!T)
    return make_error<StringError>(Msg, inconvertibleErrorCode());
  return T;
}

Error lto::finalizeOptimizationRemarks(
    std::unique_ptr<ToolOutputFile> DiagOutputFile) {
  // Make sure we flush the diagnostic remarks file in case the linker doesn't
  // call the global destructors before exiting.
  if (!DiagOutputFile)
    return Error::success();
  DiagOutputFile->keep();
  DiagOutputFile->os().flush();
  return Error::success();
}

Error lto::backend(const Config &C, AddStreamFn AddStream,
                   unsigned ParallelCodeGenParallelismLevel, Module &Mod,
                   ModuleSummaryIndex &CombinedIndex) {
  Expected<const Target *> TOrErr = initAndLookupTarget(C, Mod);
  if (!TOrErr)
    return TOrErr.takeError();

  std::unique_ptr<TargetMachine> TM = createTargetMachine(C, *TOrErr, Mod);

  LLVM_DEBUG(dbgs() << "Running regular LTO\n");
  if (!C.CodeGenOnly) {
    if (!opt(C, TM.get(), 0, Mod, /*IsThinLTO=*/false,
             /*ExportSummary=*/&CombinedIndex, /*ImportSummary=*/nullptr,
             /*CmdArgs*/ std::vector<uint8_t>()))
      return Error::success();
  }

  if (ParallelCodeGenParallelismLevel == 1) {
    codegen(C, TM.get(), AddStream, 0, Mod, CombinedIndex);
  } else {
    splitCodeGen(C, TM.get(), AddStream, ParallelCodeGenParallelismLevel, Mod,
                 CombinedIndex);
  }
  return Error::success();
}

static void dropDeadSymbols(Module &Mod, const GVSummaryMapTy &DefinedGlobals,
                            const ModuleSummaryIndex &Index) {
  std::vector<GlobalValue*> DeadGVs;
  for (auto &GV : Mod.global_values())
    if (GlobalValueSummary *GVS = DefinedGlobals.lookup(GV.getGUID()))
      if (!Index.isGlobalValueLive(GVS)) {
        DeadGVs.push_back(&GV);
        convertToDeclaration(GV);
      }

  // Now that all dead bodies have been dropped, delete the actual objects
  // themselves when possible.
  for (GlobalValue *GV : DeadGVs) {
    GV->removeDeadConstantUsers();
    // Might reference something defined in native object (i.e. dropped a
    // non-prevailing IR def, but we need to keep the declaration).
    if (GV->use_empty())
      GV->eraseFromParent();
  }
}

static void updateIndexSummaryForExternalizedGV(ModuleSummaryIndex &Index,
                                                GlobalValue &GV) {
  if (GV.hasLocalLinkage()) {
    auto VI = Index.getValueInfo(GV.getGUID());
    if (VI) {
      for (auto &S : VI.getSummaryList()) {
        S->setLinkage(GlobalValue::ExternalLinkage);
        S->setVisibility(GlobalValue::HiddenVisibility);
      }
    }
  }
}

void updateIndexSummaryForExternalizedModules(ModuleSummaryIndex &CombinedIndex,
                                              Module &M) {
  StringRef ModPath = M.getModuleIdentifier();

  struct GUIDMove {
    uint64_t OldGUID;
    uint64_t NewGUID;
    GlobalValue *GV;
    std::unique_ptr<GlobalValueSummary> Summary;
  };
  std::vector<GUIDMove> ToMove;

  for (GlobalValue &GV : M.global_values()) {
    if (!GV.hasLocalLinkage())
      continue;
    if (GV.isDeclaration())
      continue;

    uint64_t OldGUID = GV.getGUID();
    if (!GV.hasName())
      GV.setName("__llvmsplit_unnamed");

    GlobalValue::GUID NewGUID = GlobalValue::getGUID(GV.getName());
    if (OldGUID == NewGUID)
      continue;
    LLVM_DEBUG(dbgs() << "change " << GV.getName() << " from " << OldGUID
                      << " to " << NewGUID << "\n");

    auto MapIt = CombinedIndex.getGlobalValueMap().find(OldGUID);
    if (MapIt == CombinedIndex.getGlobalValueMap().end())
      continue;
    auto &Summaries = MapIt->second.SummaryList;

    for (auto It = Summaries.begin(); It != Summaries.end();) {
      if ((*It)->modulePath() == ModPath) {
        (*It)->setLinkage(GlobalValue::ExternalLinkage);
        (*It)->setVisibility(GlobalValue::HiddenVisibility);
        ToMove.push_back({OldGUID, NewGUID, &GV, std::move(*It)});
        It = Summaries.erase(It);
        break;
      } else {
        ++It;
      }
    }
    if (Summaries.empty()) {
      CombinedIndex.getGlobalValueMap().erase(MapIt);
    }
  }
  for (auto &Move : ToMove) {
    ValueInfo NewVI = CombinedIndex.getOrInsertValueInfo(Move.NewGUID);
    CombinedIndex.addGlobalValueSummary(NewVI, std::move(Move.Summary));
  }
}

static void
updateIndexSummaryForInternalizeSymbol(ModuleSummaryIndex &CombinedIndex,
                                       Module &M) {
  StringRef ModPath = M.getModuleIdentifier();

  for (auto &Entry : CombinedIndex) {
    ValueInfo VI = CombinedIndex.getValueInfo(Entry.first);
    if (!VI)
      continue;

    for (auto &S : VI.getSummaryList()) {
      if (S->modulePath() == ModPath) {
        if (GlobalValue::isLocalLinkage(S->linkage())) {
          S->setLinkage(GlobalValue::ExternalLinkage);
          S->setVisibility(GlobalValue::HiddenVisibility);
        }
      }
    }
  }
}

Error lto::thinBackend(const Config &Conf, unsigned Task, AddStreamFn AddStream,
                       Module &Mod, ModuleSummaryIndex &CombinedIndex,
                       const FunctionImporter::ImportMapTy &ImportList,
                       const GVSummaryMapTy &DefinedGlobals,
                       MapVector<StringRef, BitcodeModule> *ModuleMap,
                       std::vector<std::vector<SmallString<0>>> &bufPart,
                       const std::vector<uint8_t> &CmdArgs,
                       ThreadPool *PartitionThreadPool) {
  Expected<const Target *> TOrErr = initAndLookupTarget(Conf, Mod);
  if (!TOrErr)
    return TOrErr.takeError();

  std::unique_ptr<TargetMachine> TM = createTargetMachine(Conf, *TOrErr, Mod);

  // Setup optimization remarks.
  auto DiagFileOrErr = lto::setupLLVMOptimizationRemarks(
      Mod.getContext(), Conf.RemarksFilename, Conf.RemarksPasses,
      Conf.RemarksFormat, Conf.RemarksWithHotness, Conf.RemarksHotnessThreshold,
      Task);
  if (!DiagFileOrErr)
    return DiagFileOrErr.takeError();
  auto DiagnosticOutputFile = std::move(*DiagFileOrErr);

  // Set the partial sample profile ratio in the profile summary module flag of
  // the module, if applicable.
  Mod.setPartialSampleProfileRatio(CombinedIndex);

  if (ThinLTOSplit)
    runProfileLoaderPass(Conf, Mod, TM.get());

  if (Conf.CodeGenOnly) {
    if (ThinLTOSplit)
      if (ThinLTOCombineOutput)
        splitOptAndCodeGenThin(Task, Conf, TM.get(), AddStream,
                               ThinLTOSplitPartitions, Mod, CombinedIndex,
                               CmdArgs, PartitionThreadPool, false);
      else
        splitCodeGenThin(Task, Conf, TM.get(), AddStream,
                         ThinLTOSplitPartitions, Mod, CombinedIndex,
                         PartitionThreadPool, bufPart);
    else
      codegen(Conf, TM.get(), AddStream, Task, Mod, CombinedIndex);
    return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));
  }

  if (Conf.PreOptModuleHook && !Conf.PreOptModuleHook(Task, Mod))
    return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));

  bool ProfitableToSplit = true;
  if (ThinLTOSplit) {
    if (!canDoSplitModule(Mod)) {
      ProfitableToSplit = false;
      LLVM_DEBUG(dbgs() << "warning: thinlto split not enable for module: "
                        << Mod.getName());
    } else {
      LLVM_DEBUG(dbgs() << "thinlto: split codegen for module: "
                        << Mod.getName());
    }
  }

  auto OptimizeAndCodegen = [&](Module &Mod, TargetMachine *TM,
                                std::unique_ptr<ToolOutputFile>
                                    DiagnosticOutputFile) {
    if (ThinLTOSplit && ProfitableToSplit) {
      if (ThinLTOCombineOutput) {
        if (splitOptAndCodeGen) {
          if (!splitOptAndCodeGenThin(
                  Task, Conf, TM, AddStream, ThinLTOSplitPartitions, Mod,
                  CombinedIndex, CmdArgs, PartitionThreadPool, true))
            return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));
        } else {
          if (!opt(Conf, TM, Task, Mod, /*IsThinLTO=*/true,
                   /*ExportSummary=*/nullptr, /*ImportSummary=*/&CombinedIndex,
                   CmdArgs))
            return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));

          splitOptAndCodeGenThin(Task, Conf, TM, AddStream,
                                 ThinLTOSplitPartitions, Mod, CombinedIndex,
                                 CmdArgs, PartitionThreadPool, false);
        }
      } else {
        if (!opt(Conf, TM, Task, Mod, /*IsThinLTO=*/true,
                 /*ExportSummary=*/nullptr, /*ImportSummary=*/&CombinedIndex,
                 CmdArgs))
          return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));
        splitCodeGenThin(Task, Conf, TM, AddStream, ThinLTOSplitPartitions, Mod,
                         CombinedIndex, PartitionThreadPool, bufPart);
      }
    } else {
      if (!opt(Conf, TM, Task, Mod, /*IsThinLTO=*/true,
               /*ExportSummary=*/nullptr, /*ImportSummary=*/&CombinedIndex,
               CmdArgs))
        return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));

      codegen(Conf, TM, AddStream, Task, Mod, CombinedIndex);
    }

    return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));
  };

  if (ThinLTOAssumeMerged)
    return OptimizeAndCodegen(Mod, TM.get(), std::move(DiagnosticOutputFile));

  // When linking an ELF shared object, dso_local should be dropped. We
  // conservatively do this for -fpic.
  bool ClearDSOLocalOnDeclarations =
      TM->getTargetTriple().isOSBinFormatELF() &&
      TM->getRelocationModel() != Reloc::Static &&
      Mod.getPIELevel() == PIELevel::Default;
  renameModuleForThinLTO(Mod, CombinedIndex, ClearDSOLocalOnDeclarations);

  dropDeadSymbols(Mod, DefinedGlobals, CombinedIndex);

  thinLTOFinalizeInModule(Mod, DefinedGlobals, /*PropagateAttrs=*/true);

  if (Conf.PostPromoteModuleHook && !Conf.PostPromoteModuleHook(Task, Mod))
    return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));

  if (!DefinedGlobals.empty())
    thinLTOInternalizeModule(Mod, DefinedGlobals);

  if (Conf.PostInternalizeModuleHook &&
      !Conf.PostInternalizeModuleHook(Task, Mod))
    return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));

  auto ModuleLoader = [&](StringRef Identifier) {
    assert(Mod.getContext().isODRUniquingDebugTypes() &&
           "ODR Type uniquing should be enabled on the context");
    if (ModuleMap) {
      auto I = ModuleMap->find(Identifier);
      assert(I != ModuleMap->end());
      return I->second.getLazyModule(Mod.getContext(),
                                     /*ShouldLazyLoadMetadata=*/true,
                                     /*IsImporting*/ true);
    }

    ErrorOr<std::unique_ptr<llvm::MemoryBuffer>> MBOrErr =
        llvm::MemoryBuffer::getFile(Identifier);
    if (!MBOrErr)
      return Expected<std::unique_ptr<llvm::Module>>(make_error<StringError>(
          Twine("Error loading imported file ") + Identifier + " : ",
          MBOrErr.getError()));

    Expected<BitcodeModule> BMOrErr = findThinLTOModule(**MBOrErr);
    if (!BMOrErr)
      return Expected<std::unique_ptr<llvm::Module>>(make_error<StringError>(
          Twine("Error loading imported file ") + Identifier + " : " +
              toString(BMOrErr.takeError()),
          inconvertibleErrorCode()));

    Expected<std::unique_ptr<Module>> MOrErr =
        BMOrErr->getLazyModule(Mod.getContext(),
                               /*ShouldLazyLoadMetadata=*/true,
                               /*IsImporting*/ true);
    if (MOrErr)
      (*MOrErr)->setOwnedMemoryBuffer(std::move(*MBOrErr));
    return MOrErr;
  };

  FunctionImporter Importer(CombinedIndex, ModuleLoader,
                            ClearDSOLocalOnDeclarations);
  if (Error Err = Importer.importFunctions(Mod, ImportList).takeError())
    return Err;

  // Do this after any importing so that imported code is updated.
  updateMemProfAttributes(Mod, CombinedIndex);
  updatePublicTypeTestCalls(Mod, CombinedIndex.withWholeProgramVisibility());

  if (Conf.PostImportModuleHook && !Conf.PostImportModuleHook(Task, Mod))
    return finalizeOptimizationRemarks(std::move(DiagnosticOutputFile));

  return OptimizeAndCodegen(Mod, TM.get(), std::move(DiagnosticOutputFile));
}

BitcodeModule *lto::findThinLTOModule(MutableArrayRef<BitcodeModule> BMs) {
  if (ThinLTOAssumeMerged && BMs.size() == 1)
    return BMs.begin();

  for (BitcodeModule &BM : BMs) {
    Expected<BitcodeLTOInfo> LTOInfo = BM.getLTOInfo();
    if (LTOInfo && LTOInfo->IsThinLTO)
      return &BM;
  }
  return nullptr;
}

Expected<BitcodeModule> lto::findThinLTOModule(MemoryBufferRef MBRef) {
  Expected<std::vector<BitcodeModule>> BMsOrErr = getBitcodeModuleList(MBRef);
  if (!BMsOrErr)
    return BMsOrErr.takeError();

  // The bitcode file may contain multiple modules, we want the one that is
  // marked as being the ThinLTO module.
  if (const BitcodeModule *Bm = lto::findThinLTOModule(*BMsOrErr))
    return *Bm;

  return make_error<StringError>("Could not find module summary",
                                 inconvertibleErrorCode());
}

bool lto::initImportList(const Module &M,
                         const ModuleSummaryIndex &CombinedIndex,
                         FunctionImporter::ImportMapTy &ImportList) {
  if (ThinLTOAssumeMerged)
    return true;
  // We can simply import the values mentioned in the combined index, since
  // we should only invoke this using the individual indexes written out
  // via a WriteIndexesThinBackend.
  for (const auto &GlobalList : CombinedIndex) {
    // Ignore entries for undefined references.
    if (GlobalList.second.SummaryList.empty())
      continue;

    auto GUID = GlobalList.first;
    for (const auto &Summary : GlobalList.second.SummaryList) {
      // Skip the summaries for the importing module. These are included to
      // e.g. record required linkage changes.
      if (Summary->modulePath() == M.getModuleIdentifier())
        continue;
      // Add an entry to provoke importing by thinBackend.
      ImportList[Summary->modulePath()].insert(GUID);
    }
  }
  return true;
}
