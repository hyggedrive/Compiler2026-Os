//===- Driver.cpp ---------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The driver drives the entire linking process. It is responsible for
// parsing command line options and doing whatever it is instructed to do.
//
// One notable thing in the LLD's driver when compared to other linkers is
// that the LLD's driver is agnostic on the host operating system.
// Other linkers usually have implicit default values (such as a dynamic
// linker path or library paths) for each host OS.
//
// I don't think implicit default values are useful because they are
// usually explicitly specified by the compiler ctx.driver. They can even
// be harmful when you are doing cross-linking. Therefore, in LLD, we
// simply trust the compiler driver to pass all required options and
// don't try to make effort on our side.
//
//===----------------------------------------------------------------------===//

#include "Driver.h"
#include "Config.h"
#include "ICF.h"
#include "InputFiles.h"
#include "InputSection.h"
#include "LTO.h"
#include "LinkerScript.h"
#include "MarkLive.h"
#include "OutputSections.h"
#include "ScriptParser.h"
#include "SymbolTable.h"
#include "Symbols.h"
#include "SyntheticSections.h"
#include "Target.h"
#include "Writer.h"
#include "lld/Common/Args.h"
#include "lld/Common/CommonLinkerContext.h"
#include "lld/Common/Driver.h"
#include "lld/Common/ErrorHandler.h"
#include "lld/Common/Filesystem.h"
#include "lld/Common/Memory.h"
#include "lld/Common/Strings.h"
#include "lld/Common/TargetOptionsCommandFlags.h"
#include "lld/Common/Version.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/LTO/LTO.h"
#include "llvm/Object/Archive.h"
#include "llvm/Remarks/HotnessThresholdParser.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Compression.h"
#include "llvm/Support/Endian.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/GlobPattern.h"
#include "llvm/Support/LEB128.h"
#include "llvm/Support/Parallel.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/TarWriter.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/TimeProfiler.h"
#include "llvm/Support/raw_ostream.h"
#include <array>
#include <bitset>
#include <cstdlib>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <tuple>
#include <utility>

using namespace llvm;
using namespace llvm::ELF;
using namespace llvm::object;
using namespace llvm::sys;
using namespace llvm::support;
using namespace lld;
using namespace lld::elf;

ConfigWrapper elf::config;
Ctx elf::ctx;

static void setConfigs(opt::InputArgList &args);
static void readConfigs(opt::InputArgList &args);

void elf::errorOrWarn(const Twine &msg) {
  if (config->noinhibitExec)
    warn(msg);
  else
    error(msg);
}

void Ctx::reset() {
  driver = LinkerDriver();
  memoryBuffers.clear();
  objectFiles.clear();
  sharedFiles.clear();
  binaryFiles.clear();
  bitcodeFiles.clear();
  lazyBitcodeFiles.clear();
  inputSections.clear();
  ehInputSections.clear();
  duplicates.clear();
  nonPrevailingSyms.clear();
  whyExtractRecords.clear();
  backwardReferences.clear();
  hasSympart.store(false, std::memory_order_relaxed);
  needsTlsLd.store(false, std::memory_order_relaxed);
  ltoAllVtablesHaveTypeInfos = false;
}

llvm::raw_fd_ostream Ctx::openAuxiliaryFile(llvm::StringRef filename,
                                            std::error_code &ec) {
  using namespace llvm::sys::fs;
  OpenFlags flags =
      auxiliaryFiles.insert(filename).second ? OF_None : OF_Append;
  return {filename, ec, flags};
}

namespace lld {
namespace elf {
bool link(ArrayRef<const char *> args, llvm::raw_ostream &stdoutOS,
          llvm::raw_ostream &stderrOS, bool exitEarly, bool disableOutput) {
  // This driver-specific context will be freed later by unsafeLldMain().
  auto *ctx = new CommonLinkerContext;

  ctx->e.initialize(stdoutOS, stderrOS, exitEarly, disableOutput);
  ctx->e.cleanupCallback = []() {
    elf::ctx.reset();
    symtab = SymbolTable();

    outputSections.clear();
    symAux.clear();

    tar = nullptr;
    in.reset();

    partitions.clear();
    partitions.emplace_back();

    SharedFile::vernauxNum = 0;
  };
  ctx->e.logName = args::getFilenameWithoutExe(args[0]);
  ctx->e.errorLimitExceededMsg = "too many errors emitted, stopping now (use "
                                 "--error-limit=0 to see all errors)";

  config = ConfigWrapper();
  script = std::make_unique<LinkerScript>();

  symAux.emplace_back();

  partitions.clear();
  partitions.emplace_back();

  config->progName = args[0];

  elf::ctx.driver.linkerMain(args);

  return errorCount() == 0;
}
} // namespace elf
} // namespace lld

// Parses a linker -m option.
static std::tuple<ELFKind, uint16_t, uint8_t> parseEmulation(StringRef emul) {
  uint8_t osabi = 0;
  StringRef s = emul;
  if (s.ends_with("_fbsd")) {
    s = s.drop_back(5);
    osabi = ELFOSABI_FREEBSD;
  }

  std::pair<ELFKind, uint16_t> ret =
      StringSwitch<std::pair<ELFKind, uint16_t>>(s)
          .Cases("aarch64elf", "aarch64linux", {ELF64LEKind, EM_AARCH64})
          .Cases("aarch64elfb", "aarch64linuxb", {ELF64BEKind, EM_AARCH64})
          .Cases("armelf", "armelf_linux_eabi", {ELF32LEKind, EM_ARM})
          .Cases("armelfb", "armelfb_linux_eabi", {ELF32BEKind, EM_ARM})
          .Case("elf32_x86_64", {ELF32LEKind, EM_X86_64})
          .Cases("elf32btsmip", "elf32btsmipn32", {ELF32BEKind, EM_MIPS})
          .Cases("elf32ltsmip", "elf32ltsmipn32", {ELF32LEKind, EM_MIPS})
          .Case("elf32lriscv", {ELF32LEKind, EM_RISCV})
          .Cases("elf32ppc", "elf32ppclinux", {ELF32BEKind, EM_PPC})
          .Cases("elf32lppc", "elf32lppclinux", {ELF32LEKind, EM_PPC})
          .Case("elf32loongarch", {ELF32LEKind, EM_LOONGARCH})
          .Case("elf64btsmip", {ELF64BEKind, EM_MIPS})
          .Case("elf64ltsmip", {ELF64LEKind, EM_MIPS})
          .Case("elf64lriscv", {ELF64LEKind, EM_RISCV})
          .Case("elf64ppc", {ELF64BEKind, EM_PPC64})
          .Case("elf64lppc", {ELF64LEKind, EM_PPC64})
          .Cases("elf_amd64", "elf_x86_64", {ELF64LEKind, EM_X86_64})
          .Case("elf_i386", {ELF32LEKind, EM_386})
          .Case("elf_iamcu", {ELF32LEKind, EM_IAMCU})
          .Case("elf64_sparc", {ELF64BEKind, EM_SPARCV9})
          .Case("msp430elf", {ELF32LEKind, EM_MSP430})
          .Case("elf64_amdgpu", {ELF64LEKind, EM_AMDGPU})
          .Case("elf64loongarch", {ELF64LEKind, EM_LOONGARCH})
          .Cases("elf64-sw_64", "elf64sw_64", {ELF64LEKind, EM_SW64})
          .Default({ELFNoneKind, EM_NONE});

  if (ret.first == ELFNoneKind)
    error("unknown emulation: " + emul);
  if (ret.second == EM_MSP430)
    osabi = ELFOSABI_STANDALONE;
  else if (ret.second == EM_AMDGPU)
    osabi = ELFOSABI_AMDGPU_HSA;
  return std::make_tuple(ret.first, ret.second, osabi);
}

// Returns slices of MB by parsing MB as an archive file.
// Each slice consists of a member file in the archive.
std::vector<std::pair<MemoryBufferRef, uint64_t>> static getArchiveMembers(
    MemoryBufferRef mb) {
  std::unique_ptr<Archive> file =
      CHECK(Archive::create(mb),
            mb.getBufferIdentifier() + ": failed to parse archive");

  std::vector<std::pair<MemoryBufferRef, uint64_t>> v;
  Error err = Error::success();
  bool addToTar = file->isThin() && tar;
  for (const Archive::Child &c : file->children(err)) {
    MemoryBufferRef mbref =
        CHECK(c.getMemoryBufferRef(),
              mb.getBufferIdentifier() +
                  ": could not get the buffer for a child of the archive");
    if (addToTar)
      tar->append(relativeToRoot(check(c.getFullName())), mbref.getBuffer());
    v.push_back(std::make_pair(mbref, c.getChildOffset()));
  }
  if (err)
    fatal(mb.getBufferIdentifier() + ": Archive::children failed: " +
          toString(std::move(err)));

  // Take ownership of memory buffers created for members of thin archives.
  std::vector<std::unique_ptr<MemoryBuffer>> mbs = file->takeThinBuffers();
  std::move(mbs.begin(), mbs.end(), std::back_inserter(ctx.memoryBuffers));

  return v;
}

static bool isBitcode(MemoryBufferRef mb) {
  return identify_magic(mb.getBuffer()) == llvm::file_magic::bitcode;
}

// Opens a file and create a file object. Path has to be resolved already.
void LinkerDriver::addFile(StringRef path, bool withLOption) {
  using namespace sys::fs;

  std::optional<MemoryBufferRef> buffer = readFile(path);
  if (!buffer)
    return;
  MemoryBufferRef mbref = *buffer;

  if (config->formatBinary) {
    files.push_back(make<BinaryFile>(mbref));
    return;
  }

  switch (identify_magic(mbref.getBuffer())) {
  case file_magic::unknown:
    readLinkerScript(mbref);
    return;
  case file_magic::archive: {
    auto members = getArchiveMembers(mbref);
    if (inWholeArchive) {
      for (const std::pair<MemoryBufferRef, uint64_t> &p : members) {
        if (isBitcode(p.first))
          files.push_back(make<BitcodeFile>(p.first, path, p.second, false));
        else
          files.push_back(createObjFile(p.first, path));
      }
      return;
    }

    archiveFiles.emplace_back(path, members.size());

    // Handle archives and --start-lib/--end-lib using the same code path. This
    // scans all the ELF relocatable object files and bitcode files in the
    // archive rather than just the index file, with the benefit that the
    // symbols are only loaded once. For many projects archives see high
    // utilization rates and it is a net performance win. --start-lib scans
    // symbols in the same order that llvm-ar adds them to the index, so in the
    // common case the semantics are identical. If the archive symbol table was
    // created in a different order, or is incomplete, this strategy has
    // different semantics. Such output differences are considered user error.
    //
    // All files within the archive get the same group ID to allow mutual
    // references for --warn-backrefs.
    bool saved = InputFile::isInGroup;
    InputFile::isInGroup = true;
    for (const std::pair<MemoryBufferRef, uint64_t> &p : members) {
      auto magic = identify_magic(p.first.getBuffer());
      if (magic == file_magic::elf_relocatable)
        files.push_back(createObjFile(p.first, path, true));
      else if (magic == file_magic::bitcode)
        files.push_back(make<BitcodeFile>(p.first, path, p.second, true));
      else
        warn(path + ": archive member '" + p.first.getBufferIdentifier() +
             "' is neither ET_REL nor LLVM bitcode");
    }
    InputFile::isInGroup = saved;
    if (!saved)
      ++InputFile::nextGroupId;
    return;
  }
  case file_magic::elf_shared_object: {
    if (config->isStatic || config->relocatable) {
      error("attempted static link of dynamic object " + path);
      return;
    }

    // Shared objects are identified by soname. soname is (if specified)
    // DT_SONAME and falls back to filename. If a file was specified by -lfoo,
    // the directory part is ignored. Note that path may be a temporary and
    // cannot be stored into SharedFile::soName.
    path = mbref.getBufferIdentifier();
    auto *f =
        make<SharedFile>(mbref, withLOption ? path::filename(path) : path);
    f->init();
    files.push_back(f);
    return;
  }
  case file_magic::bitcode:
    files.push_back(make<BitcodeFile>(mbref, "", 0, inLib));
    break;
  case file_magic::elf_relocatable:
    files.push_back(createObjFile(mbref, "", inLib));
    break;
  default:
    error(path + ": unknown file type");
  }
}

// Add a given library by searching it from input search paths.
void LinkerDriver::addLibrary(StringRef name) {
  if (std::optional<std::string> path = searchLibrary(name))
    addFile(saver().save(*path), /*withLOption=*/true);
  else
    error("unable to find library -l" + name, ErrorTag::LibNotFound, {name});
}

// This function is called on startup. We need this for LTO since
// LTO calls LLVM functions to compile bitcode files to native code.
// Technically this can be delayed until we read bitcode files, but
// we don't bother to do lazily because the initialization is fast.
static void initLLVM() {
#if defined(ENABLE_AUTOTUNER)
  // AUTO-TUNING - initialization
  if (Error E = autotuning::Engine.init(config->outputFile.data())) {
    error(toString(std::move(E)));
    return;
  }
  if (autotuning::Engine.isEnabled() && autotuning::Engine.isParseInput() &&
      (autotuning::Engine.LLVMParams.size() ||
       autotuning::Engine.ProgramParams.size()))
    llvm::cl::ParseAutoTunerOptions(autotuning::Engine.LLVMParams,
                                    autotuning::Engine.ProgramParams);
#endif
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmPrinters();
  InitializeAllAsmParsers();
}

// Some command line options or some combinations of them are not allowed.
// This function checks for such errors.
static void checkOptions() {
  // The MIPS ABI as of 2016 does not support the GNU-style symbol lookup
  // table which is a relatively new feature.
  if (config->emachine == EM_MIPS && config->gnuHash)
    error("the .gnu.hash section is not compatible with the MIPS target");

  if (config->emachine == EM_ARM) {
    if (!config->cmseImplib) {
      if (!config->cmseInputLib.empty())
        error("--in-implib may not be used without --cmse-implib");
      if (!config->cmseOutputLib.empty())
        error("--out-implib may not be used without --cmse-implib");
    }
  } else {
    if (config->cmseImplib)
      error("--cmse-implib is only supported on ARM targets");
    if (!config->cmseInputLib.empty())
      error("--in-implib is only supported on ARM targets");
    if (!config->cmseOutputLib.empty())
      error("--out-implib is only supported on ARM targets");
  }

  if (config->fixCortexA53Errata843419 && config->emachine != EM_AARCH64)
    error("--fix-cortex-a53-843419 is only supported on AArch64 targets");

  if (config->fixCortexA8 && config->emachine != EM_ARM)
    error("--fix-cortex-a8 is only supported on ARM targets");

  if (config->armBe8 && config->emachine != EM_ARM)
    error("--be8 is only supported on ARM targets");

  if (config->fixCortexA8 && !config->isLE)
    error("--fix-cortex-a8 is not supported on big endian targets");

  if (config->tocOptimize && config->emachine != EM_PPC64)
    error("--toc-optimize is only supported on PowerPC64 targets");

  if (config->pcRelOptimize && config->emachine != EM_PPC64)
    error("--pcrel-optimize is only supported on PowerPC64 targets");

  if (config->relaxGP && config->emachine != EM_RISCV)
    error("--relax-gp is only supported on RISC-V targets");

  if (config->pie && config->shared)
    error("-shared and -pie may not be used together");

  if (!config->shared && !config->filterList.empty())
    error("-F may not be used without -shared");

  if (!config->shared && !config->auxiliaryList.empty())
    error("-f may not be used without -shared");

  if (config->strip == StripPolicy::All && config->emitRelocs)
    error("--strip-all and --emit-relocs may not be used together");

  if (config->zText && config->zIfuncNoplt)
    error("-z text and -z ifunc-noplt may not be used together");

  if (config->relocatable) {
    if (config->shared)
      error("-r and -shared may not be used together");
    if (config->gdbIndex)
      error("-r and --gdb-index may not be used together");
    if (config->icf != ICFLevel::None)
      error("-r and --icf may not be used together");
    if (config->pie)
      error("-r and -pie may not be used together");
    if (config->exportDynamic)
      error("-r and --export-dynamic may not be used together");
  }

  if (config->executeOnly) {
    if (config->emachine != EM_AARCH64)
      error("--execute-only is only supported on AArch64 targets");

    if (config->singleRoRx && !script->hasSectionsCommand)
      error("--execute-only and --no-rosegment cannot be used together");
  }

  if (config->zRetpolineplt && config->zForceIbt)
    error("-z force-ibt may not be used with -z retpolineplt");

  if (config->emachine != EM_AARCH64) {
    if (config->zPacPlt)
      error("-z pac-plt only supported on AArch64");
    if (config->zForceBti)
      error("-z force-bti only supported on AArch64");
    if (config->zBtiReport != "none")
      error("-z bti-report only supported on AArch64");
  }

  if (config->emachine != EM_386 && config->emachine != EM_X86_64 &&
      config->zCetReport != "none")
    error("-z cet-report only supported on X86 and X86_64");
}

static const char *getReproduceOption(opt::InputArgList &args) {
  if (auto *arg = args.getLastArg(OPT_reproduce))
    return arg->getValue();
  return getenv("LLD_REPRODUCE");
}

static bool hasZOption(opt::InputArgList &args, StringRef key) {
  for (auto *arg : args.filtered(OPT_z))
    if (key == arg->getValue())
      return true;
  return false;
}

static bool getZFlag(opt::InputArgList &args, StringRef k1, StringRef k2,
                     bool Default) {
  for (auto *arg : args.filtered_reverse(OPT_z)) {
    if (k1 == arg->getValue())
      return true;
    if (k2 == arg->getValue())
      return false;
  }
  return Default;
}

static SeparateSegmentKind getZSeparate(opt::InputArgList &args) {
  for (auto *arg : args.filtered_reverse(OPT_z)) {
    StringRef v = arg->getValue();
    if (v == "noseparate-code")
      return SeparateSegmentKind::None;
    if (v == "separate-code")
      return SeparateSegmentKind::Code;
    if (v == "separate-loadable-segments")
      return SeparateSegmentKind::Loadable;
  }
  return SeparateSegmentKind::None;
}

static GnuStackKind getZGnuStack(opt::InputArgList &args) {
  for (auto *arg : args.filtered_reverse(OPT_z)) {
    if (StringRef("execstack") == arg->getValue())
      return GnuStackKind::Exec;
    if (StringRef("noexecstack") == arg->getValue())
      return GnuStackKind::NoExec;
    if (StringRef("nognustack") == arg->getValue())
      return GnuStackKind::None;
  }

  return GnuStackKind::NoExec;
}

static uint8_t getZStartStopVisibility(opt::InputArgList &args) {
  for (auto *arg : args.filtered_reverse(OPT_z)) {
    std::pair<StringRef, StringRef> kv = StringRef(arg->getValue()).split('=');
    if (kv.first == "start-stop-visibility") {
      if (kv.second == "default")
        return STV_DEFAULT;
      else if (kv.second == "internal")
        return STV_INTERNAL;
      else if (kv.second == "hidden")
        return STV_HIDDEN;
      else if (kv.second == "protected")
        return STV_PROTECTED;
      error("unknown -z start-stop-visibility= value: " + StringRef(kv.second));
    }
  }
  return STV_PROTECTED;
}

constexpr const char *knownZFlags[] = {
    "combreloc",
    "copyreloc",
    "defs",
    "execstack",
    "force-bti",
    "force-ibt",
    "global",
    "hazardplt",
    "ifunc-noplt",
    "initfirst",
    "interpose",
    "keep-text-section-prefix",
    "lazy",
    "muldefs",
    "nocombreloc",
    "nocopyreloc",
    "nodefaultlib",
    "nodelete",
    "nodlopen",
    "noexecstack",
    "nognustack",
    "nokeep-text-section-prefix",
    "nopack-relative-relocs",
    "norelro",
    "noseparate-code",
    "nostart-stop-gc",
    "notext",
    "now",
    "origin",
    "pac-plt",
    "pack-relative-relocs",
    "rel",
    "rela",
    "relro",
    "retpolineplt",
    "rodynamic",
    "separate-code",
    "separate-loadable-segments",
    "shstk",
    "start-stop-gc",
    "text",
    "undefs",
    "wxneeded",
    "oe-aware",
};

static bool isKnownZFlag(StringRef s) {
  return llvm::is_contained(knownZFlags, s) ||
         s.starts_with("common-page-size=") || s.starts_with("bti-report=") ||
         s.starts_with("cet-report=") ||
         s.starts_with("dead-reloc-in-nonalloc=") ||
         s.starts_with("max-page-size=") || s.starts_with("stack-size=") ||
         s.starts_with("start-stop-visibility=");
}

// Report a warning for an unknown -z option.
static void checkZOptions(opt::InputArgList &args) {
  for (auto *arg : args.filtered(OPT_z))
    if (!isKnownZFlag(arg->getValue()))
      warn("unknown -z value: " + StringRef(arg->getValue()));
}

constexpr const char *saveTempsValues[] = {
    "resolution", "preopt",     "promote", "internalize",  "import",
    "opt",        "precodegen", "prelink", "combinedindex"};

void LinkerDriver::linkerMain(ArrayRef<const char *> argsArr) {
  ELFOptTable parser;
  opt::InputArgList args = parser.parse(argsArr.slice(1));

  // Interpret these flags early because error()/warn() depend on them.
  errorHandler().errorLimit = args::getInteger(args, OPT_error_limit, 20);
  errorHandler().fatalWarnings =
      args.hasFlag(OPT_fatal_warnings, OPT_no_fatal_warnings, false) &&
      !args.hasArg(OPT_no_warnings);
  errorHandler().suppressWarnings = args.hasArg(OPT_no_warnings);
  checkZOptions(args);

  // Handle -help
  if (args.hasArg(OPT_help)) {
    printHelp();
    return;
  }

  // Handle -v or -version.
  //
  // A note about "compatible with GNU linkers" message: this is a hack for
  // scripts generated by GNU Libtool up to 2021-10 to recognize LLD as
  // a GNU compatible linker. See
  // <https://lists.gnu.org/archive/html/libtool/2017-01/msg00007.html>.
  //
  // This is somewhat ugly hack, but in reality, we had no choice other
  // than doing this. Considering the very long release cycle of Libtool,
  // it is not easy to improve it to recognize LLD as a GNU compatible
  // linker in a timely manner. Even if we can make it, there are still a
  // lot of "configure" scripts out there that are generated by old version
  // of Libtool. We cannot convince every software developer to migrate to
  // the latest version and re-generate scripts. So we have this hack.
  if (args.hasArg(OPT_v) || args.hasArg(OPT_version))
    message(getLLDVersion() + " (compatible with GNU linkers)");

  if (const char *path = getReproduceOption(args)) {
    // Note that --reproduce is a debug option so you can ignore it
    // if you are trying to understand the whole picture of the code.
    Expected<std::unique_ptr<TarWriter>> errOrWriter =
        TarWriter::create(path, path::stem(path));
    if (errOrWriter) {
      tar = std::move(*errOrWriter);
      tar->append("response.txt", createResponseFile(args));
      tar->append("version.txt", getLLDVersion() + "\n");
      StringRef ltoSampleProfile = args.getLastArgValue(OPT_lto_sample_profile);
      if (!ltoSampleProfile.empty())
        readFile(ltoSampleProfile);
    } else {
      error("--reproduce: " + toString(errOrWriter.takeError()));
    }
  }

  readConfigs(args);

  // The behavior of -v or --version is a bit strange, but this is
  // needed for compatibility with GNU linkers.
  if (args.hasArg(OPT_v) && !args.hasArg(OPT_INPUT))
    return;
  if (args.hasArg(OPT_version))
    return;

  // Initialize time trace profiler.
  if (config->timeTraceEnabled)
    timeTraceProfilerInitialize(config->timeTraceGranularity, config->progName);

  {
    llvm::TimeTraceScope timeScope("ExecuteLinker");

    initLLVM();
    createFiles(args);
    if (errorCount())
      return;

    inferMachineType();
    setConfigs(args);
    checkOptions();
    if (errorCount())
      return;

    link(args);
  }

  if (config->timeTraceEnabled) {
    checkError(timeTraceProfilerWrite(
        args.getLastArgValue(OPT_time_trace_eq).str(), config->outputFile));
    timeTraceProfilerCleanup();
  }
}

static std::string getRpath(opt::InputArgList &args) {
  SmallVector<StringRef, 0> v = args::getStrings(args, OPT_rpath);
  return llvm::join(v.begin(), v.end(), ":");
}

// Determines what we should do if there are remaining unresolved
// symbols after the name resolution.
static void setUnresolvedSymbolPolicy(opt::InputArgList &args) {
  UnresolvedPolicy errorOrWarn = args.hasFlag(OPT_error_unresolved_symbols,
                                              OPT_warn_unresolved_symbols, true)
                                     ? UnresolvedPolicy::ReportError
                                     : UnresolvedPolicy::Warn;
  // -shared implies --unresolved-symbols=ignore-all because missing
  // symbols are likely to be resolved at runtime.
  bool diagRegular = !config->shared, diagShlib = !config->shared;

  for (const opt::Arg *arg : args) {
    switch (arg->getOption().getID()) {
    case OPT_unresolved_symbols: {
      StringRef s = arg->getValue();
      if (s == "ignore-all") {
        diagRegular = false;
        diagShlib = false;
      } else if (s == "ignore-in-object-files") {
        diagRegular = false;
        diagShlib = true;
      } else if (s == "ignore-in-shared-libs") {
        diagRegular = true;
        diagShlib = false;
      } else if (s == "report-all") {
        diagRegular = true;
        diagShlib = true;
      } else {
        error("unknown --unresolved-symbols value: " + s);
      }
      break;
    }
    case OPT_no_undefined:
      diagRegular = true;
      break;
    case OPT_z:
      if (StringRef(arg->getValue()) == "defs")
        diagRegular = true;
      else if (StringRef(arg->getValue()) == "undefs")
        diagRegular = false;
      break;
    case OPT_allow_shlib_undefined:
      diagShlib = false;
      break;
    case OPT_no_allow_shlib_undefined:
      diagShlib = true;
      break;
    }
  }

  config->unresolvedSymbols =
      diagRegular ? errorOrWarn : UnresolvedPolicy::Ignore;
  config->unresolvedSymbolsInShlib =
      diagShlib ? errorOrWarn : UnresolvedPolicy::Ignore;
}

static Target2Policy getTarget2(opt::InputArgList &args) {
  StringRef s = args.getLastArgValue(OPT_target2, "got-rel");
  if (s == "rel")
    return Target2Policy::Rel;
  if (s == "abs")
    return Target2Policy::Abs;
  if (s == "got-rel")
    return Target2Policy::GotRel;
  error("unknown --target2 option: " + s);
  return Target2Policy::GotRel;
}

static bool isOutputFormatBinary(opt::InputArgList &args) {
  StringRef s = args.getLastArgValue(OPT_oformat, "elf");
  if (s == "binary")
    return true;
  if (!s.starts_with("elf"))
    error("unknown --oformat value: " + s);
  return false;
}

static DiscardPolicy getDiscard(opt::InputArgList &args) {
  auto *arg =
      args.getLastArg(OPT_discard_all, OPT_discard_locals, OPT_discard_none);
  if (!arg)
    return DiscardPolicy::Default;
  if (arg->getOption().getID() == OPT_discard_all)
    return DiscardPolicy::All;
  if (arg->getOption().getID() == OPT_discard_locals)
    return DiscardPolicy::Locals;
  return DiscardPolicy::None;
}

static StringRef getDynamicLinker(opt::InputArgList &args) {
  auto *arg = args.getLastArg(OPT_dynamic_linker, OPT_no_dynamic_linker);
  if (!arg)
    return "";
  if (arg->getOption().getID() == OPT_no_dynamic_linker) {
    // --no-dynamic-linker suppresses undefined weak symbols in .dynsym
    config->noDynamicLinker = true;
    return "";
  }
  return arg->getValue();
}

static int getMemtagMode(opt::InputArgList &args) {
  StringRef memtagModeArg = args.getLastArgValue(OPT_android_memtag_mode);
  if (memtagModeArg.empty()) {
    if (config->androidMemtagStack)
      warn("--android-memtag-mode is unspecified, leaving "
           "--android-memtag-stack a no-op");
    else if (config->androidMemtagHeap)
      warn("--android-memtag-mode is unspecified, leaving "
           "--android-memtag-heap a no-op");
    return ELF::NT_MEMTAG_LEVEL_NONE;
  }

  if (!config->androidMemtagHeap && !config->androidMemtagStack) {
    error("when using --android-memtag-mode, at least one of "
          "--android-memtag-heap or "
          "--android-memtag-stack is required");
    return ELF::NT_MEMTAG_LEVEL_NONE;
  }

  if (memtagModeArg == "sync")
    return ELF::NT_MEMTAG_LEVEL_SYNC;
  if (memtagModeArg == "async")
    return ELF::NT_MEMTAG_LEVEL_ASYNC;
  if (memtagModeArg == "none")
    return ELF::NT_MEMTAG_LEVEL_NONE;

  error("unknown --android-memtag-mode value: \"" + memtagModeArg +
        "\", should be one of {async, sync, none}");
  return ELF::NT_MEMTAG_LEVEL_NONE;
}

static ICFLevel getICF(opt::InputArgList &args) {
  auto *arg = args.getLastArg(OPT_icf_none, OPT_icf_safe, OPT_icf_all);
  if (!arg || arg->getOption().getID() == OPT_icf_none)
    return ICFLevel::None;
  if (arg->getOption().getID() == OPT_icf_safe)
    return ICFLevel::Safe;
  return ICFLevel::All;
}

static StripPolicy getStrip(opt::InputArgList &args) {
  if (args.hasArg(OPT_relocatable))
    return StripPolicy::None;

  auto *arg = args.getLastArg(OPT_strip_all, OPT_strip_debug);
  if (!arg)
    return StripPolicy::None;
  if (arg->getOption().getID() == OPT_strip_all)
    return StripPolicy::All;
  return StripPolicy::Debug;
}

static uint64_t parseSectionAddress(StringRef s, opt::InputArgList &args,
                                    const opt::Arg &arg) {
  uint64_t va = 0;
  if (s.starts_with("0x"))
    s = s.drop_front(2);
  if (!to_integer(s, va, 16))
    error("invalid argument: " + arg.getAsString(args));
  return va;
}

static StringMap<uint64_t> getSectionStartMap(opt::InputArgList &args) {
  StringMap<uint64_t> ret;
  for (auto *arg : args.filtered(OPT_section_start)) {
    StringRef name;
    StringRef addr;
    std::tie(name, addr) = StringRef(arg->getValue()).split('=');
    ret[name] = parseSectionAddress(addr, args, *arg);
  }

  if (auto *arg = args.getLastArg(OPT_Ttext))
    ret[".text"] = parseSectionAddress(arg->getValue(), args, *arg);
  if (auto *arg = args.getLastArg(OPT_Tdata))
    ret[".data"] = parseSectionAddress(arg->getValue(), args, *arg);
  if (auto *arg = args.getLastArg(OPT_Tbss))
    ret[".bss"] = parseSectionAddress(arg->getValue(), args, *arg);
  return ret;
}

static SortSectionPolicy getSortSection(opt::InputArgList &args) {
  StringRef s = args.getLastArgValue(OPT_sort_section);
  if (s == "alignment")
    return SortSectionPolicy::Alignment;
  if (s == "name")
    return SortSectionPolicy::Name;
  if (!s.empty())
    error("unknown --sort-section rule: " + s);
  return SortSectionPolicy::Default;
}

static OrphanHandlingPolicy getOrphanHandling(opt::InputArgList &args) {
  StringRef s = args.getLastArgValue(OPT_orphan_handling, "place");
  if (s == "warn")
    return OrphanHandlingPolicy::Warn;
  if (s == "error")
    return OrphanHandlingPolicy::Error;
  if (s != "place")
    error("unknown --orphan-handling mode: " + s);
  return OrphanHandlingPolicy::Place;
}

// Parse --build-id or --build-id=<style>. We handle "tree" as a
// synonym for "sha1" because all our hash functions including
// --build-id=sha1 are actually tree hashes for performance reasons.
static std::pair<BuildIdKind, SmallVector<uint8_t, 0>>
getBuildId(opt::InputArgList &args) {
  auto *arg = args.getLastArg(OPT_build_id);
  if (!arg)
    return {BuildIdKind::None, {}};

  StringRef s = arg->getValue();
  if (s == "fast")
    return {BuildIdKind::Fast, {}};
  if (s == "md5")
    return {BuildIdKind::Md5, {}};
  if (s == "sha1" || s == "tree")
    return {BuildIdKind::Sha1, {}};
  if (s == "uuid")
    return {BuildIdKind::Uuid, {}};
  if (s.starts_with("0x"))
    return {BuildIdKind::Hexstring, parseHex(s.substr(2))};

  if (s != "none")
    error("unknown --build-id style: " + s);
  return {BuildIdKind::None, {}};
}

static std::pair<bool, bool> getPackDynRelocs(opt::InputArgList &args) {
  StringRef s = args.getLastArgValue(OPT_pack_dyn_relocs, "none");
  if (s == "android")
    return {true, false};
  if (s == "relr")
    return {false, true};
  if (s == "android+relr")
    return {true, true};

  if (s != "none")
    error("unknown --pack-dyn-relocs format: " + s);
  return {false, false};
}

static void readCallGraph(MemoryBufferRef mb) {
  // Build a map from symbol name to section
  DenseMap<StringRef, Symbol *> map;
  for (ELFFileBase *file : ctx.objectFiles)
    for (Symbol *sym : file->getSymbols())
      map[sym->getName()] = sym;

  auto findSection = [&](StringRef name) -> InputSectionBase * {
    Symbol *sym = map.lookup(name);
    if (!sym) {
      if (config->warnSymbolOrdering)
        warn(mb.getBufferIdentifier() + ": no such symbol: " + name);
      return nullptr;
    }
    maybeWarnUnorderableSymbol(sym);

    if (Defined *dr = dyn_cast_or_null<Defined>(sym))
      return dyn_cast_or_null<InputSectionBase>(dr->section);
    return nullptr;
  };

  for (StringRef line : args::getLines(mb)) {
    SmallVector<StringRef, 3> fields;
    line.split(fields, ' ');
    uint64_t count;

    if (fields.size() != 3 || !to_integer(fields[2], count)) {
      error(mb.getBufferIdentifier() + ": parse error");
      return;
    }

    if (InputSectionBase *from = findSection(fields[0]))
      if (InputSectionBase *to = findSection(fields[1]))
        config->callGraphProfile[std::make_pair(from, to)] += count;
  }
}

// If SHT_LLVM_CALL_GRAPH_PROFILE and its relocation section exist, returns
// true and populates cgProfile and symbolIndices.
template <class ELFT>
static bool
processCallGraphRelocations(SmallVector<uint32_t, 32> &symbolIndices,
                            ArrayRef<typename ELFT::CGProfile> &cgProfile,
                            ObjFile<ELFT> *inputObj) {
  if (inputObj->cgProfileSectionIndex == SHN_UNDEF)
    return false;

  ArrayRef<Elf_Shdr_Impl<ELFT>> objSections =
      inputObj->template getELFShdrs<ELFT>();
  symbolIndices.clear();
  const ELFFile<ELFT> &obj = inputObj->getObj();
  cgProfile =
      check(obj.template getSectionContentsAsArray<typename ELFT::CGProfile>(
          objSections[inputObj->cgProfileSectionIndex]));

  for (size_t i = 0, e = objSections.size(); i < e; ++i) {
    const Elf_Shdr_Impl<ELFT> &sec = objSections[i];
    if (sec.sh_info == inputObj->cgProfileSectionIndex) {
      if (sec.sh_type == SHT_RELA) {
        ArrayRef<typename ELFT::Rela> relas =
            CHECK(obj.relas(sec), "could not retrieve cg profile rela section");
        for (const typename ELFT::Rela &rel : relas)
          symbolIndices.push_back(rel.getSymbol(config->isMips64EL));
        break;
      }
      if (sec.sh_type == SHT_REL) {
        ArrayRef<typename ELFT::Rel> rels =
            CHECK(obj.rels(sec), "could not retrieve cg profile rel section");
        for (const typename ELFT::Rel &rel : rels)
          symbolIndices.push_back(rel.getSymbol(config->isMips64EL));
        break;
      }
    }
  }
  if (symbolIndices.empty())
    warn("SHT_LLVM_CALL_GRAPH_PROFILE exists, but relocation section doesn't");
  return !symbolIndices.empty();
}

template <class ELFT> static void readCallGraphsFromObjectFiles() {
  SmallVector<uint32_t, 32> symbolIndices;
  ArrayRef<typename ELFT::CGProfile> cgProfile;
  for (auto file : ctx.objectFiles) {
    auto *obj = cast<ObjFile<ELFT>>(file);
    if (!processCallGraphRelocations(symbolIndices, cgProfile, obj))
      continue;

    if (symbolIndices.size() != cgProfile.size() * 2)
      fatal("number of relocations doesn't match Weights");

    for (uint32_t i = 0, size = cgProfile.size(); i < size; ++i) {
      const Elf_CGProfile_Impl<ELFT> &cgpe = cgProfile[i];
      uint32_t fromIndex = symbolIndices[i * 2];
      uint32_t toIndex = symbolIndices[i * 2 + 1];
      auto *fromSym = dyn_cast<Defined>(&obj->getSymbol(fromIndex));
      auto *toSym = dyn_cast<Defined>(&obj->getSymbol(toIndex));
      if (!fromSym || !toSym)
        continue;

      auto *from = dyn_cast_or_null<InputSectionBase>(fromSym->section);
      auto *to = dyn_cast_or_null<InputSectionBase>(toSym->section);
      if (from && to)
        config->callGraphProfile[{from, to}] += cgpe.cgp_weight;
    }
  }
}

template <class ELFT>
static void ltoValidateAllVtablesHaveTypeInfos(opt::InputArgList &args) {
  DenseSet<StringRef> typeInfoSymbols;
  SmallSetVector<StringRef, 0> vtableSymbols;
  auto processVtableAndTypeInfoSymbols = [&](StringRef name) {
    if (name.consume_front("_ZTI"))
      typeInfoSymbols.insert(name);
    else if (name.consume_front("_ZTV"))
      vtableSymbols.insert(name);
  };

  // Examine all native symbol tables.
  for (ELFFileBase *f : ctx.objectFiles) {
    using Elf_Sym = typename ELFT::Sym;
    for (const Elf_Sym &s : f->template getGlobalELFSyms<ELFT>()) {
      if (s.st_shndx != SHN_UNDEF) {
        StringRef name = check(s.getName(f->getStringTable()));
        processVtableAndTypeInfoSymbols(name);
      }
    }
  }

  for (SharedFile *f : ctx.sharedFiles) {
    using Elf_Sym = typename ELFT::Sym;
    for (const Elf_Sym &s : f->template getELFSyms<ELFT>()) {
      if (s.st_shndx != SHN_UNDEF) {
        StringRef name = check(s.getName(f->getStringTable()));
        processVtableAndTypeInfoSymbols(name);
      }
    }
  }

  SmallSetVector<StringRef, 0> vtableSymbolsWithNoRTTI;
  for (StringRef s : vtableSymbols)
    if (!typeInfoSymbols.count(s))
      vtableSymbolsWithNoRTTI.insert(s);

  // Remove known safe symbols.
  for (auto *arg : args.filtered(OPT_lto_known_safe_vtables)) {
    StringRef knownSafeName = arg->getValue();
    if (!knownSafeName.consume_front("_ZTV"))
      error("--lto-known-safe-vtables=: expected symbol to start with _ZTV, "
            "but got " +
            knownSafeName);
    vtableSymbolsWithNoRTTI.remove(knownSafeName);
  }

  ctx.ltoAllVtablesHaveTypeInfos = vtableSymbolsWithNoRTTI.empty();
  // Check for unmatched RTTI symbols
  for (StringRef s : vtableSymbolsWithNoRTTI) {
    message(
        "--lto-validate-all-vtables-have-type-infos: RTTI missing for vtable "
        "_ZTV" +
        s + ", --lto-whole-program-visibility disabled");
  }
}

static CGProfileSortKind getCGProfileSortKind(opt::InputArgList &args) {
  StringRef s = args.getLastArgValue(OPT_call_graph_profile_sort, "hfsort");
  if (s == "hfsort")
    return CGProfileSortKind::Hfsort;
  if (s == "cdsort")
    return CGProfileSortKind::Cdsort;
  if (s != "none")
    error("unknown --call-graph-profile-sort= value: " + s);
  return CGProfileSortKind::None;
}

static DebugCompressionType getCompressionType(StringRef s, StringRef option) {
  DebugCompressionType type = StringSwitch<DebugCompressionType>(s)
                                  .Case("zlib", DebugCompressionType::Zlib)
                                  .Case("zstd", DebugCompressionType::Zstd)
                                  .Default(DebugCompressionType::None);
  if (type == DebugCompressionType::None) {
    if (s != "none")
      error("unknown " + option + " value: " + s);
  } else if (const char *reason = compression::getReasonIfUnsupported(
                 compression::formatFor(type))) {
    error(option + ": " + reason);
  }
  return type;
}

static StringRef getAliasSpelling(opt::Arg *arg) {
  if (const opt::Arg *alias = arg->getAlias())
    return alias->getSpelling();
  return arg->getSpelling();
}

static std::pair<StringRef, StringRef> getOldNewOptions(opt::InputArgList &args,
                                                        unsigned id) {
  auto *arg = args.getLastArg(id);
  if (!arg)
    return {"", ""};

  StringRef s = arg->getValue();
  std::pair<StringRef, StringRef> ret = s.split(';');
  if (ret.second.empty())
    error(getAliasSpelling(arg) + " expects 'old;new' format, but got " + s);
  return ret;
}

// Parse options of the form "old;new[;extra]".
static std::tuple<StringRef, StringRef, StringRef>
getOldNewOptionsExtra(opt::InputArgList &args, unsigned id) {
  auto [oldDir, second] = getOldNewOptions(args, id);
  auto [newDir, extraDir] = second.split(';');
  return {oldDir, newDir, extraDir};
}

// Parse the symbol ordering file and warn for any duplicate entries.
static SmallVector<StringRef, 0> getSymbolOrderingFile(MemoryBufferRef mb) {
  SetVector<StringRef, SmallVector<StringRef, 0>> names;
  for (StringRef s : args::getLines(mb))
    if (!names.insert(s) && config->warnSymbolOrdering)
      warn(mb.getBufferIdentifier() + ": duplicate ordered symbol: " + s);

  return names.takeVector();
}

static bool getIsRela(opt::InputArgList &args) {
  // If -z rel or -z rela is specified, use the last option.
  for (auto *arg : args.filtered_reverse(OPT_z)) {
    StringRef s(arg->getValue());
    if (s == "rel")
      return false;
    if (s == "rela")
      return true;
  }

  // Otherwise use the psABI defined relocation entry format.
  uint16_t m = config->emachine;
  return m == EM_AARCH64 || m == EM_AMDGPU || m == EM_HEXAGON ||
         m == EM_LOONGARCH || m == EM_PPC || m == EM_PPC64 || m == EM_RISCV ||
         m == EM_SW64 || m == EM_X86_64;
}

static void parseClangOption(StringRef opt, const Twine &msg) {
  std::string err;
  raw_string_ostream os(err);

  const char *argv[] = {config->progName.data(), opt.data()};
  if (cl::ParseCommandLineOptions(2, argv, "", &os))
    return;
  os.flush();
  error(msg + ": " + StringRef(err).trim());
}

// Checks the parameter of the bti-report and cet-report options.
static bool isValidReportString(StringRef arg) {
  return arg == "none" || arg == "warning" || arg == "error";
}

// Process a remap pattern 'from-glob=to-file'.
static bool remapInputs(StringRef line, const Twine &location) {
  SmallVector<StringRef, 0> fields;
  line.split(fields, '=');
  if (fields.size() != 2 || fields[1].empty()) {
    error(location + ": parse error, not 'from-glob=to-file'");
    return true;
  }
  if (!hasWildcard(fields[0]))
    config->remapInputs[fields[0]] = fields[1];
  else if (Expected<GlobPattern> pat = GlobPattern::create(fields[0]))
    config->remapInputsWildcards.emplace_back(std::move(*pat), fields[1]);
  else {
    error(location + ": " + toString(pat.takeError()));
    return true;
  }
  return false;
}

// Initializes Config members by the command line options.
static void readConfigs(opt::InputArgList &args) {
  errorHandler().verbose = args.hasArg(OPT_verbose);
  errorHandler().vsDiagnostics =
      args.hasArg(OPT_visual_studio_diagnostics_format, false);

  config->allowMultipleDefinition =
      args.hasFlag(OPT_allow_multiple_definition,
                   OPT_no_allow_multiple_definition, false) ||
      hasZOption(args, "muldefs");
  config->androidMemtagHeap =
      args.hasFlag(OPT_android_memtag_heap, OPT_no_android_memtag_heap, false);
  config->androidMemtagStack = args.hasFlag(OPT_android_memtag_stack,
                                            OPT_no_android_memtag_stack, false);
  config->androidMemtagMode = getMemtagMode(args);
  config->auxiliaryList = args::getStrings(args, OPT_auxiliary);
  config->armBe8 = args.hasArg(OPT_be8);
  if (opt::Arg *arg =
          args.getLastArg(OPT_Bno_symbolic, OPT_Bsymbolic_non_weak_functions,
                          OPT_Bsymbolic_functions, OPT_Bsymbolic)) {
    if (arg->getOption().matches(OPT_Bsymbolic_non_weak_functions))
      config->bsymbolic = BsymbolicKind::NonWeakFunctions;
    else if (arg->getOption().matches(OPT_Bsymbolic_functions))
      config->bsymbolic = BsymbolicKind::Functions;
    else if (arg->getOption().matches(OPT_Bsymbolic))
      config->bsymbolic = BsymbolicKind::All;
  }
  config->callGraphProfileSort = getCGProfileSortKind(args);
  config->checkSections =
      args.hasFlag(OPT_check_sections, OPT_no_check_sections, true);
  config->chroot = args.getLastArgValue(OPT_chroot);
  config->compressDebugSections = getCompressionType(
      args.getLastArgValue(OPT_compress_debug_sections, "none"),
      "--compress-debug-sections");
  config->cref = args.hasArg(OPT_cref);
  config->optimizeBBJumps =
      args.hasFlag(OPT_optimize_bb_jumps, OPT_no_optimize_bb_jumps, false);
  config->demangle = args.hasFlag(OPT_demangle, OPT_no_demangle, true);
  config->dependencyFile = args.getLastArgValue(OPT_dependency_file);
  config->dependentLibraries = args.hasFlag(OPT_dependent_libraries, OPT_no_dependent_libraries, true);
  config->disableVerify = args.hasArg(OPT_disable_verify);
  config->discard = getDiscard(args);
  config->dwoDir = args.getLastArgValue(OPT_plugin_opt_dwo_dir_eq);
  config->dynamicLinker = getDynamicLinker(args);
  config->ehFrameHdr =
      args.hasFlag(OPT_eh_frame_hdr, OPT_no_eh_frame_hdr, false);
  config->emitLLVM = args.hasArg(OPT_plugin_opt_emit_llvm, false);
  config->emitRelocs = args.hasArg(OPT_emit_relocs);
  config->enableNewDtags =
      args.hasFlag(OPT_enable_new_dtags, OPT_disable_new_dtags, true);
  config->entry = args.getLastArgValue(OPT_entry);

  errorHandler().errorHandlingScript =
      args.getLastArgValue(OPT_error_handling_script);

  config->executeOnly =
      args.hasFlag(OPT_execute_only, OPT_no_execute_only, false);
  config->exportDynamic =
      args.hasFlag(OPT_export_dynamic, OPT_no_export_dynamic, false) ||
      args.hasArg(OPT_shared);
  config->filterList = args::getStrings(args, OPT_filter);
  config->fini = args.getLastArgValue(OPT_fini, "_fini");
  config->fixCortexA53Errata843419 = args.hasArg(OPT_fix_cortex_a53_843419) &&
                                     !args.hasArg(OPT_relocatable);
  config->cmseImplib = args.hasArg(OPT_cmse_implib);
  config->cmseInputLib = args.getLastArgValue(OPT_in_implib);
  config->cmseOutputLib = args.getLastArgValue(OPT_out_implib);
  config->fixCortexA8 =
      args.hasArg(OPT_fix_cortex_a8) && !args.hasArg(OPT_relocatable);
  config->fortranCommon =
      args.hasFlag(OPT_fortran_common, OPT_no_fortran_common, false);
  config->gcSections = args.hasFlag(OPT_gc_sections, OPT_no_gc_sections, false);
  config->gnuUnique = args.hasFlag(OPT_gnu_unique, OPT_no_gnu_unique, true);
  config->gdbIndex = args.hasFlag(OPT_gdb_index, OPT_no_gdb_index, false);
  config->icf = getICF(args);
  config->ignoreDataAddressEquality =
      args.hasArg(OPT_ignore_data_address_equality);
  config->ignoreFunctionAddressEquality =
      args.hasArg(OPT_ignore_function_address_equality);
  config->init = args.getLastArgValue(OPT_init, "_init");
  config->ltoAAPipeline = args.getLastArgValue(OPT_lto_aa_pipeline);
  config->ltoCSProfileGenerate = args.hasArg(OPT_lto_cs_profile_generate);
  config->ltoCSProfileFile = args.getLastArgValue(OPT_lto_cs_profile_file);
  config->ltoPGOWarnMismatch = args.hasFlag(OPT_lto_pgo_warn_mismatch,
                                            OPT_no_lto_pgo_warn_mismatch, true);
  config->ltoDebugPassManager = args.hasArg(OPT_lto_debug_pass_manager);
  config->ltoEmitAsm = args.hasArg(OPT_lto_emit_asm);
  config->ltoNewPmPasses = args.getLastArgValue(OPT_lto_newpm_passes);
  config->ltoWholeProgramVisibility =
      args.hasFlag(OPT_lto_whole_program_visibility,
                   OPT_no_lto_whole_program_visibility, false);
  config->ltoValidateAllVtablesHaveTypeInfos =
      args.hasFlag(OPT_lto_validate_all_vtables_have_type_infos,
                   OPT_no_lto_validate_all_vtables_have_type_infos, false);
  config->ltoo = args::getInteger(args, OPT_lto_O, 2);
  if (config->ltoo > 3)
    error("invalid optimization level for LTO: " + Twine(config->ltoo));
  unsigned ltoCgo =
      args::getInteger(args, OPT_lto_CGO, args::getCGOptLevel(config->ltoo));
  if (auto level = CodeGenOpt::getLevel(ltoCgo))
    config->ltoCgo = *level;
  else
    error("invalid codegen optimization level for LTO: " + Twine(ltoCgo));
  config->ltoObjPath = args.getLastArgValue(OPT_lto_obj_path_eq);
  config->ltoPartitions = args::getInteger(args, OPT_lto_partitions, 1);
  config->ltoSampleProfile = args.getLastArgValue(OPT_lto_sample_profile);
  config->ltoBBAddrMap =
      args.hasFlag(OPT_lto_basic_block_address_map,
                   OPT_no_lto_basic_block_address_map, false);
  config->ltoBasicBlockSections =
      args.getLastArgValue(OPT_lto_basic_block_sections);
  config->ltoUniqueBasicBlockSectionNames =
      args.hasFlag(OPT_lto_unique_basic_block_section_names,
                   OPT_no_lto_unique_basic_block_section_names, false);
  config->mapFile = args.getLastArgValue(OPT_Map);
  config->mipsGotSize = args::getInteger(args, OPT_mips_got_size, 0xfff0);
  config->mergeArmExidx =
      args.hasFlag(OPT_merge_exidx_entries, OPT_no_merge_exidx_entries, true);
  config->mmapOutputFile =
      args.hasFlag(OPT_mmap_output_file, OPT_no_mmap_output_file, true);
  config->nmagic = args.hasFlag(OPT_nmagic, OPT_no_nmagic, false);
  config->noinhibitExec = args.hasArg(OPT_noinhibit_exec);
  config->nostdlib = args.hasArg(OPT_nostdlib);
  config->oFormatBinary = isOutputFormatBinary(args);
  config->omagic = args.hasFlag(OPT_omagic, OPT_no_omagic, false);
  config->optRemarksFilename = args.getLastArgValue(OPT_opt_remarks_filename);
  config->optStatsFilename = args.getLastArgValue(OPT_plugin_opt_stats_file);

  // Parse remarks hotness threshold. Valid value is either integer or 'auto'.
  if (auto *arg = args.getLastArg(OPT_opt_remarks_hotness_threshold)) {
    auto resultOrErr = remarks::parseHotnessThresholdOption(arg->getValue());
    if (!resultOrErr)
      error(arg->getSpelling() + ": invalid argument '" + arg->getValue() +
            "', only integer or 'auto' is supported");
    else
      config->optRemarksHotnessThreshold = *resultOrErr;
  }

  config->optRemarksPasses = args.getLastArgValue(OPT_opt_remarks_passes);
  config->optRemarksWithHotness = args.hasArg(OPT_opt_remarks_with_hotness);
  config->optRemarksFormat = args.getLastArgValue(OPT_opt_remarks_format);
  config->optimize = args::getInteger(args, OPT_O, 1);
  config->orphanHandling = getOrphanHandling(args);
  config->outputFile = args.getLastArgValue(OPT_o);
  config->packageMetadata = args.getLastArgValue(OPT_package_metadata);
  config->pie = args.hasFlag(OPT_pie, OPT_no_pie, false);
  config->printIcfSections =
      args.hasFlag(OPT_print_icf_sections, OPT_no_print_icf_sections, false);
  config->printGcSections =
      args.hasFlag(OPT_print_gc_sections, OPT_no_print_gc_sections, false);
  config->printMemoryUsage = args.hasArg(OPT_print_memory_usage);
  config->printRISCVLibcSpecializationAudit =
      args.hasArg(OPT_print_riscv_libc_specialization_audit);
  config->riscvPrintfSpecialization =
      args.hasArg(OPT_riscv_printf_specialization);
  config->riscvLibcSpecializationAuditDumpFailedCalls = args::getInteger(
      args, OPT_riscv_libc_specialization_audit_dump_failed_calls, 0);
  config->riscvLibcSpecializationAuditDumpCallOffsets =
      args.getLastArgValue(OPT_riscv_libc_specialization_audit_dump_call_offsets);
  config->printRISCVFunctionSectionsSplit =
      args.hasArg(OPT_print_riscv_function_sections_split);
  config->printArchiveStats = args.getLastArgValue(OPT_print_archive_stats);
  config->printSymbolOrder =
      args.getLastArgValue(OPT_print_symbol_order);
  config->relax = args.hasFlag(OPT_relax, OPT_no_relax, true);
  config->relaxGP = args.hasFlag(OPT_relax_gp, OPT_no_relax_gp, false);
  config->riscvRelaxJalRVC =
      args.hasFlag(OPT_riscv_relax_jal_rvc,
                   OPT_no_riscv_relax_jal_rvc, false);
  config->riscvFunctionSectionsSplitDebugRelocs =
      args.hasFlag(OPT_riscv_function_sections_split_debug_relocs,
                   OPT_no_riscv_function_sections_split_debug_relocs, false);
  config->riscvFunctionSectionsSplitICF =
      args.hasFlag(OPT_riscv_function_sections_split_icf,
                   OPT_no_riscv_function_sections_split_icf, false);
  config->riscvFunctionSectionsSplitGC =
      args.hasFlag(OPT_riscv_function_sections_split_gc,
                   OPT_no_riscv_function_sections_split_gc, false);
  config->riscvFunctionSectionsSplitGC =
      config->riscvFunctionSectionsSplitGC ||
      config->riscvFunctionSectionsSplitDebugRelocs ||
      config->riscvFunctionSectionsSplitICF;

  config->riscvFunctionSectionsSplit =
      args.hasArg(OPT_riscv_function_sections_split) ||
      config->riscvFunctionSectionsSplitGC;
  config->rpath = getRpath(args);
  config->relocatable = args.hasArg(OPT_relocatable);

  if (args.hasArg(OPT_save_temps)) {
    // --save-temps implies saving all temps.
    for (const char *s : saveTempsValues)
      config->saveTempsArgs.insert(s);
  } else {
    for (auto *arg : args.filtered(OPT_save_temps_eq)) {
      StringRef s = arg->getValue();
      if (llvm::is_contained(saveTempsValues, s))
        config->saveTempsArgs.insert(s);
      else
        error("unknown --save-temps value: " + s);
    }
  }

  config->searchPaths = args::getStrings(args, OPT_library_path);
  config->sectionStartMap = getSectionStartMap(args);
  config->shared = args.hasArg(OPT_shared);
  config->singleRoRx = !args.hasFlag(OPT_rosegment, OPT_no_rosegment, true);
  config->soName = args.getLastArgValue(OPT_soname);
  config->sortSection = getSortSection(args);
  config->splitStackAdjustSize = args::getInteger(args, OPT_split_stack_adjust_size, 16384);
  config->strip = getStrip(args);
  config->sysroot = args.getLastArgValue(OPT_sysroot);
  config->target1Rel = args.hasFlag(OPT_target1_rel, OPT_target1_abs, false);
  config->target2 = getTarget2(args);
  config->thinLTOCacheDir = args.getLastArgValue(OPT_thinlto_cache_dir);
  config->thinLTOCachePolicy = CHECK(
      parseCachePruningPolicy(args.getLastArgValue(OPT_thinlto_cache_policy)),
      "--thinlto-cache-policy: invalid cache policy");
  config->thinLTOEmitImportsFiles = args.hasArg(OPT_thinlto_emit_imports_files);
  config->thinLTOEmitIndexFiles = args.hasArg(OPT_thinlto_emit_index_files) ||
                                  args.hasArg(OPT_thinlto_index_only) ||
                                  args.hasArg(OPT_thinlto_index_only_eq);
  config->thinLTOIndexOnly = args.hasArg(OPT_thinlto_index_only) ||
                             args.hasArg(OPT_thinlto_index_only_eq);
  config->thinLTOIndexOnlyArg = args.getLastArgValue(OPT_thinlto_index_only_eq);
  config->thinLTOObjectSuffixReplace =
      getOldNewOptions(args, OPT_thinlto_object_suffix_replace_eq);
  std::tie(config->thinLTOPrefixReplaceOld, config->thinLTOPrefixReplaceNew,
           config->thinLTOPrefixReplaceNativeObject) =
      getOldNewOptionsExtra(args, OPT_thinlto_prefix_replace_eq);
  if (config->thinLTOEmitIndexFiles && !config->thinLTOIndexOnly) {
    if (args.hasArg(OPT_thinlto_object_suffix_replace_eq))
      error("--thinlto-object-suffix-replace is not supported with "
            "--thinlto-emit-index-files");
    else if (args.hasArg(OPT_thinlto_prefix_replace_eq))
      error("--thinlto-prefix-replace is not supported with "
            "--thinlto-emit-index-files");
  }
  if (!config->thinLTOPrefixReplaceNativeObject.empty() &&
      config->thinLTOIndexOnlyArg.empty()) {
    error("--thinlto-prefix-replace=old_dir;new_dir;obj_dir must be used with "
          "--thinlto-index-only=");
  }
  config->thinLTOModulesToCompile =
      args::getStrings(args, OPT_thinlto_single_module_eq);
  config->timeTraceEnabled = args.hasArg(OPT_time_trace_eq);
  config->timeTraceGranularity =
      args::getInteger(args, OPT_time_trace_granularity, 500);

  config->sw64_tlsrelgot_tlsgd =
      args.hasFlag(OPT_sw64_tlsrelgot_tlsgd, OPT_no_sw64_tlsrelgot_tlsgd, false);
  config->sw64_tlsrelgot_tlsldm =
      args.hasFlag(OPT_sw64_tlsrelgot_tlsldm, OPT_no_sw64_tlsrelgot_tlsldm, false);
  config->sw64_tlsrelgot_gottprel =
      args.hasFlag(OPT_sw64_tlsrelgot_gottprel, OPT_no_sw64_tlsrelgot_gottprel, false);
  config->sw64_tlsrelgot_gotdtprel =
      args.hasFlag(OPT_sw64_tlsrelgot_gotdtprel, OPT_no_sw64_tlsrelgot_gotdtprel, false);

  config->trace = args.hasArg(OPT_trace);
  config->undefined = args::getStrings(args, OPT_undefined);
  config->undefinedVersion =
      args.hasFlag(OPT_undefined_version, OPT_no_undefined_version, false);
  config->unique = args.hasArg(OPT_unique);
  config->useAndroidRelrTags = args.hasFlag(
      OPT_use_android_relr_tags, OPT_no_use_android_relr_tags, false);
  config->warnBackrefs =
      args.hasFlag(OPT_warn_backrefs, OPT_no_warn_backrefs, false);
  config->warnCommon = args.hasFlag(OPT_warn_common, OPT_no_warn_common, false);
  config->warnSymbolOrdering =
      args.hasFlag(OPT_warn_symbol_ordering, OPT_no_warn_symbol_ordering, true);
  config->whyExtract = args.getLastArgValue(OPT_why_extract);
  config->zCombreloc = getZFlag(args, "combreloc", "nocombreloc", true);
  config->zCopyreloc = getZFlag(args, "copyreloc", "nocopyreloc", true);
  config->zForceBti = hasZOption(args, "force-bti");
  config->zForceIbt = hasZOption(args, "force-ibt");
  config->zGlobal = hasZOption(args, "global");
  config->zGnustack = getZGnuStack(args);
  config->zHazardplt = hasZOption(args, "hazardplt");
  config->zIfuncNoplt = hasZOption(args, "ifunc-noplt");
  config->zInitfirst = hasZOption(args, "initfirst");
  config->zInterpose = hasZOption(args, "interpose");
  config->zKeepTextSectionPrefix = getZFlag(
      args, "keep-text-section-prefix", "nokeep-text-section-prefix", false);
  config->zNodefaultlib = hasZOption(args, "nodefaultlib");
  config->zNodelete = hasZOption(args, "nodelete");
  config->zNodlopen = hasZOption(args, "nodlopen");
  config->zNow = getZFlag(args, "now", "lazy", false);
  config->zOrigin = hasZOption(args, "origin");
  config->zPacPlt = hasZOption(args, "pac-plt");
  config->zRelro = getZFlag(args, "relro", "norelro", true);
  config->zRetpolineplt = hasZOption(args, "retpolineplt");
  config->zRodynamic = hasZOption(args, "rodynamic");
  config->zSeparate = getZSeparate(args);
  config->zShstk = hasZOption(args, "shstk");
  config->zStackSize = args::getZOptionValue(args, OPT_z, "stack-size", 0);
  config->zStartStopGC =
      getZFlag(args, "start-stop-gc", "nostart-stop-gc", true);
  config->zStartStopVisibility = getZStartStopVisibility(args);
  config->zText = getZFlag(args, "text", "notext", true);
  config->zWxneeded = hasZOption(args, "wxneeded");
  config->zOeawarePolicy = args::getZOptionValue(args, OPT_z,  "oeaware-policy", -1);
  setUnresolvedSymbolPolicy(args);
  config->power10Stubs = args.getLastArgValue(OPT_power10_stubs_eq) != "no";

  if (opt::Arg *arg = args.getLastArg(OPT_eb, OPT_el)) {
    if (arg->getOption().matches(OPT_eb))
      config->optEB = true;
    else
      config->optEL = true;
  }

  for (opt::Arg *arg : args.filtered(OPT_remap_inputs)) {
    StringRef value(arg->getValue());
    remapInputs(value, arg->getSpelling());
  }
  for (opt::Arg *arg : args.filtered(OPT_remap_inputs_file)) {
    StringRef filename(arg->getValue());
    std::optional<MemoryBufferRef> buffer = readFile(filename);
    if (!buffer)
      continue;
    // Parse 'from-glob=to-file' lines, ignoring #-led comments.
    for (auto [lineno, line] : llvm::enumerate(args::getLines(*buffer)))
      if (remapInputs(line, filename + ":" + Twine(lineno + 1)))
        break;
  }

  for (opt::Arg *arg : args.filtered(OPT_shuffle_sections)) {
    constexpr StringRef errPrefix = "--shuffle-sections=: ";
    std::pair<StringRef, StringRef> kv = StringRef(arg->getValue()).split('=');
    if (kv.first.empty() || kv.second.empty()) {
      error(errPrefix + "expected <section_glob>=<seed>, but got '" +
            arg->getValue() + "'");
      continue;
    }
    // Signed so that <section_glob>=-1 is allowed.
    int64_t v;
    if (!to_integer(kv.second, v))
      error(errPrefix + "expected an integer, but got '" + kv.second + "'");
    else if (Expected<GlobPattern> pat = GlobPattern::create(kv.first))
      config->shuffleSections.emplace_back(std::move(*pat), uint32_t(v));
    else
      error(errPrefix + toString(pat.takeError()));
  }

  auto reports = {std::make_pair("bti-report", &config->zBtiReport),
                  std::make_pair("cet-report", &config->zCetReport)};
  for (opt::Arg *arg : args.filtered(OPT_z)) {
    std::pair<StringRef, StringRef> option =
        StringRef(arg->getValue()).split('=');
    for (auto reportArg : reports) {
      if (option.first != reportArg.first)
        continue;
      if (!isValidReportString(option.second)) {
        error(Twine("-z ") + reportArg.first + "= parameter " + option.second +
              " is not recognized");
        continue;
      }
      *reportArg.second = option.second;
    }
  }

  for (opt::Arg *arg : args.filtered(OPT_z)) {
    std::pair<StringRef, StringRef> option =
        StringRef(arg->getValue()).split('=');
    if (option.first != "dead-reloc-in-nonalloc")
      continue;
    constexpr StringRef errPrefix = "-z dead-reloc-in-nonalloc=: ";
    std::pair<StringRef, StringRef> kv = option.second.split('=');
    if (kv.first.empty() || kv.second.empty()) {
      error(errPrefix + "expected <section_glob>=<value>");
      continue;
    }
    uint64_t v;
    if (!to_integer(kv.second, v))
      error(errPrefix + "expected a non-negative integer, but got '" +
            kv.second + "'");
    else if (Expected<GlobPattern> pat = GlobPattern::create(kv.first))
      config->deadRelocInNonAlloc.emplace_back(std::move(*pat), v);
    else
      error(errPrefix + toString(pat.takeError()));
  }

  cl::ResetAllOptionOccurrences();

  // Parse LTO options.
  if (auto *arg = args.getLastArg(OPT_plugin_opt_mcpu_eq))
    parseClangOption(saver().save("-mcpu=" + StringRef(arg->getValue())),
                     arg->getSpelling());

  for (opt::Arg *arg : args.filtered(OPT_plugin_opt_eq_minus))
    parseClangOption(std::string("-") + arg->getValue(), arg->getSpelling());

  // GCC collect2 passes -plugin-opt=path/to/lto-wrapper with an absolute or
  // relative path. Just ignore. If not ended with "lto-wrapper" (or
  // "lto-wrapper.exe" for GCC cross-compiled for Windows), consider it an
  // unsupported LLVMgold.so option and error.
  for (opt::Arg *arg : args.filtered(OPT_plugin_opt_eq)) {
    StringRef v(arg->getValue());
    if (!v.ends_with("lto-wrapper") && !v.ends_with("lto-wrapper.exe"))
      error(arg->getSpelling() + ": unknown plugin option '" + arg->getValue() +
            "'");
  }

  config->passPlugins = args::getStrings(args, OPT_load_pass_plugins);

  // Parse -mllvm options.
  for (const auto *arg : args.filtered(OPT_mllvm)) {
    parseClangOption(arg->getValue(), arg->getSpelling());
    config->mllvmOpts.emplace_back(arg->getValue());
  }

  config->ltoKind = LtoKind::Default;
  if (auto *arg = args.getLastArg(OPT_lto)) {
    StringRef s = arg->getValue();
    if (s == "thin")
      config->ltoKind = LtoKind::UnifiedThin;
    else if (s == "full")
      config->ltoKind = LtoKind::UnifiedRegular;
    else if (s == "default")
      config->ltoKind = LtoKind::Default;
    else
      error("unknown LTO mode: " + s);
  }

  // --threads= takes a positive integer and provides the default value for
  // --thinlto-jobs=. If unspecified, cap the number of threads since
  // overhead outweighs optimization for used parallel algorithms for the
  // non-LTO parts.
  if (auto *arg = args.getLastArg(OPT_threads)) {
    StringRef v(arg->getValue());
    unsigned threads = 0;
    if (!llvm::to_integer(v, threads, 0) || threads == 0)
      error(arg->getSpelling() + ": expected a positive integer, but got '" +
            arg->getValue() + "'");
    parallel::strategy = hardware_concurrency(threads);
    config->thinLTOJobs = v;
  } else if (parallel::strategy.compute_thread_count() > 16) {
    log("set maximum concurrency to 16, specify --threads= to change");
    parallel::strategy = hardware_concurrency(16);
  }
  if (auto *arg = args.getLastArg(OPT_thinlto_jobs_eq))
    config->thinLTOJobs = arg->getValue();
  config->threadCount = parallel::strategy.compute_thread_count();

  if (config->ltoPartitions == 0)
    error("--lto-partitions: number of threads must be > 0");
  if (!get_threadpool_strategy(config->thinLTOJobs))
    error("--thinlto-jobs: invalid job count: " + config->thinLTOJobs);

  if (config->splitStackAdjustSize < 0)
    error("--split-stack-adjust-size: size must be >= 0");

  // The text segment is traditionally the first segment, whose address equals
  // the base address. However, lld places the R PT_LOAD first. -Ttext-segment
  // is an old-fashioned option that does not play well with lld's layout.
  // Suggest --image-base as a likely alternative.
  if (args.hasArg(OPT_Ttext_segment))
    error("-Ttext-segment is not supported. Use --image-base if you "
          "intend to set the base address");

  // Parse ELF{32,64}{LE,BE} and CPU type.
  if (auto *arg = args.getLastArg(OPT_m)) {
    StringRef s = arg->getValue();
    std::tie(config->ekind, config->emachine, config->osabi) =
        parseEmulation(s);
    config->mipsN32Abi =
        (s.starts_with("elf32btsmipn32") || s.starts_with("elf32ltsmipn32"));
    config->emulation = s;
  }

  // Parse --hash-style={sysv,gnu,both}.
  if (auto *arg = args.getLastArg(OPT_hash_style)) {
    StringRef s = arg->getValue();
    if (s == "sysv")
      config->sysvHash = true;
    else if (s == "gnu")
      config->gnuHash = true;
    else if (s == "both")
      config->sysvHash = config->gnuHash = true;
    else
      error("unknown --hash-style: " + s);
  }

  if (args.hasArg(OPT_print_map))
    config->mapFile = "-";

  // Page alignment can be disabled by the -n (--nmagic) and -N (--omagic).
  // As PT_GNU_RELRO relies on Paging, do not create it when we have disabled
  // it.
  if (config->nmagic || config->omagic)
    config->zRelro = false;

  std::tie(config->buildId, config->buildIdVector) = getBuildId(args);

  if (getZFlag(args, "pack-relative-relocs", "nopack-relative-relocs", false)) {
    config->relrGlibc = true;
    config->relrPackDynRelocs = true;
  } else {
    std::tie(config->androidPackDynRelocs, config->relrPackDynRelocs) =
        getPackDynRelocs(args);
  }

  if (auto *arg = args.getLastArg(OPT_symbol_ordering_file)){
    if (args.hasArg(OPT_call_graph_ordering_file))
      error("--symbol-ordering-file and --call-graph-order-file "
            "may not be used together");
    if (std::optional<MemoryBufferRef> buffer = readFile(arg->getValue())) {
      config->symbolOrderingFile = getSymbolOrderingFile(*buffer);
      // Also need to disable CallGraphProfileSort to prevent
      // LLD order symbols with CGProfile
      config->callGraphProfileSort = CGProfileSortKind::None;
    }
  }

  assert(config->versionDefinitions.empty());
  config->versionDefinitions.push_back(
      {"local", (uint16_t)VER_NDX_LOCAL, {}, {}});
  config->versionDefinitions.push_back(
      {"global", (uint16_t)VER_NDX_GLOBAL, {}, {}});

  // If --retain-symbol-file is used, we'll keep only the symbols listed in
  // the file and discard all others.
  if (auto *arg = args.getLastArg(OPT_retain_symbols_file)) {
    config->versionDefinitions[VER_NDX_LOCAL].nonLocalPatterns.push_back(
        {"*", /*isExternCpp=*/false, /*hasWildcard=*/true});
    if (std::optional<MemoryBufferRef> buffer = readFile(arg->getValue()))
      for (StringRef s : args::getLines(*buffer))
        config->versionDefinitions[VER_NDX_GLOBAL].nonLocalPatterns.push_back(
            {s, /*isExternCpp=*/false, /*hasWildcard=*/false});
  }

  for (opt::Arg *arg : args.filtered(OPT_warn_backrefs_exclude)) {
    StringRef pattern(arg->getValue());
    if (Expected<GlobPattern> pat = GlobPattern::create(pattern))
      config->warnBackrefsExclude.push_back(std::move(*pat));
    else
      error(arg->getSpelling() + ": " + toString(pat.takeError()));
  }

  // For -no-pie and -pie, --export-dynamic-symbol specifies defined symbols
  // which should be exported. For -shared, references to matched non-local
  // STV_DEFAULT symbols are not bound to definitions within the shared object,
  // even if other options express a symbolic intention: -Bsymbolic,
  // -Bsymbolic-functions (if STT_FUNC), --dynamic-list.
  for (auto *arg : args.filtered(OPT_export_dynamic_symbol))
    config->dynamicList.push_back(
        {arg->getValue(), /*isExternCpp=*/false,
         /*hasWildcard=*/hasWildcard(arg->getValue())});

  // --export-dynamic-symbol-list specifies a list of --export-dynamic-symbol
  // patterns. --dynamic-list is --export-dynamic-symbol-list plus -Bsymbolic
  // like semantics.
  config->symbolic =
      config->bsymbolic == BsymbolicKind::All || args.hasArg(OPT_dynamic_list);
  for (auto *arg :
       args.filtered(OPT_dynamic_list, OPT_export_dynamic_symbol_list))
    if (std::optional<MemoryBufferRef> buffer = readFile(arg->getValue()))
      readDynamicList(*buffer);

  for (auto *arg : args.filtered(OPT_version_script))
    if (std::optional<std::string> path = searchScript(arg->getValue())) {
      if (std::optional<MemoryBufferRef> buffer = readFile(*path))
        readVersionScript(*buffer);
    } else {
      error(Twine("cannot find version script ") + arg->getValue());
    }
}

// Some Config members do not directly correspond to any particular
// command line options, but computed based on other Config values.
// This function initialize such members. See Config.h for the details
// of these values.
static void setConfigs(opt::InputArgList &args) {
  ELFKind k = config->ekind;
  uint16_t m = config->emachine;

  const bool isRISCV32 = config->emachine == EM_RISCV && !config->is64;

  if (!args.hasArg(OPT_gc_sections, OPT_no_gc_sections))
    config->gcSections = isRISCV32;

  if (!args.hasArg(OPT_relax_gp, OPT_no_relax_gp))
    config->relaxGP = isRISCV32;

  if (!args.hasArg(OPT_riscv_function_sections_split_debug_relocs,
                   OPT_no_riscv_function_sections_split_debug_relocs))
    config->riscvFunctionSectionsSplitDebugRelocs = isRISCV32;

  if (!args.hasArg(OPT_riscv_function_sections_split_icf,
                   OPT_no_riscv_function_sections_split_icf))
    config->riscvFunctionSectionsSplitICF = isRISCV32;

  if (!args.hasArg(OPT_riscv_relax_jal_rvc, OPT_no_riscv_relax_jal_rvc))
    config->riscvRelaxJalRVC = isRISCV32;
  if (isRISCV32 &&
      !args.hasArg(OPT_icf_none, OPT_icf_safe, OPT_icf_all))
    config->icf = ICFLevel::Safe;

  if (!args.hasArg(OPT_riscv_function_sections_split_gc,
                   OPT_no_riscv_function_sections_split_gc))
    config->riscvFunctionSectionsSplitGC = isRISCV32;
  config->riscvFunctionSectionsSplitGC =
      config->riscvFunctionSectionsSplitGC ||
      config->riscvFunctionSectionsSplitDebugRelocs ||
      config->riscvFunctionSectionsSplitICF;
  config->riscvFunctionSectionsSplit =
      config->riscvFunctionSectionsSplit ||
      config->riscvFunctionSectionsSplitGC;

  config->copyRelocs = (config->relocatable || config->emitRelocs);
  config->is64 = (k == ELF64LEKind || k == ELF64BEKind);
  config->isLE = (k == ELF32LEKind || k == ELF64LEKind);
  config->endianness = config->isLE ? endianness::little : endianness::big;
  config->isMips64EL = (k == ELF64LEKind && m == EM_MIPS);
  config->isPic = config->pie || config->shared;
  config->picThunk = args.hasArg(OPT_pic_veneer, config->isPic);
  config->wordsize = config->is64 ? 8 : 4;

  if (m == EM_RISCV && !config->is64 &&
      config->riscvFunctionSectionsSplitDebugRelocs &&
      llvm::none_of(config->deadRelocInNonAlloc,
                    [](const std::pair<GlobPattern, uint64_t> &patAndValue) {
                      return patAndValue.first.match(".debug_info");
                    })) {
    Expected<GlobPattern> pat = GlobPattern::create(".debug_info");
    if (!pat)
      error(toString(pat.takeError()));
    else
      config->deadRelocInNonAlloc.emplace_back(std::move(*pat), 0xffffffff);
  }

  // ELF defines two different ways to store relocation addends as shown below:
  //
  //  Rel: Addends are stored to the location where relocations are applied. It
  //  cannot pack the full range of addend values for all relocation types, but
  //  this only affects relocation types that we don't support emitting as
  //  dynamic relocations (see getDynRel).
  //  Rela: Addends are stored as part of relocation entry.
  //
  // In other words, Rela makes it easy to read addends at the price of extra
  // 4 or 8 byte for each relocation entry.
  //
  // We pick the format for dynamic relocations according to the psABI for each
  // processor, but a contrary choice can be made if the dynamic loader
  // supports.
  config->isRela = getIsRela(args);

  // If the output uses REL relocations we must store the dynamic relocation
  // addends to the output sections. We also store addends for RELA relocations
  // if --apply-dynamic-relocs is used.
  // We default to not writing the addends when using RELA relocations since
  // any standard conforming tool can find it in r_addend.
  config->writeAddends = args.hasFlag(OPT_apply_dynamic_relocs,
                                      OPT_no_apply_dynamic_relocs, false) ||
                         !config->isRela;
  // Validation of dynamic relocation addends is on by default for assertions
  // builds (for supported targets) and disabled otherwise. Ideally we would
  // enable the debug checks for all targets, but currently not all targets
  // have support for reading Elf_Rel addends, so we only enable for a subset.
#ifndef NDEBUG
  bool checkDynamicRelocsDefault = m == EM_AARCH64 || m == EM_ARM ||
                                   m == EM_386 || m == EM_LOONGARCH ||
                                   m == EM_MIPS || m == EM_RISCV ||
                                   m == EM_X86_64;
#else
  bool checkDynamicRelocsDefault = false;
#endif
  config->checkDynamicRelocs =
      args.hasFlag(OPT_check_dynamic_relocations,
                   OPT_no_check_dynamic_relocations, checkDynamicRelocsDefault);
  config->tocOptimize =
      args.hasFlag(OPT_toc_optimize, OPT_no_toc_optimize, m == EM_PPC64);
  config->pcRelOptimize =
      args.hasFlag(OPT_pcrel_optimize, OPT_no_pcrel_optimize, m == EM_PPC64);
}

static bool isFormatBinary(StringRef s) {
  if (s == "binary")
    return true;
  if (s == "elf" || s == "default")
    return false;
  error("unknown --format value: " + s +
        " (supported formats: elf, default, binary)");
  return false;
}

void LinkerDriver::createFiles(opt::InputArgList &args) {
  llvm::TimeTraceScope timeScope("Load input files");
  // For --{push,pop}-state.
  std::vector<std::tuple<bool, bool, bool>> stack;

  // Iterate over argv to process input files and positional arguments.
  InputFile::isInGroup = false;
  bool hasInput = false;
  for (auto *arg : args) {
    switch (arg->getOption().getID()) {
    case OPT_library:
      addLibrary(arg->getValue());
      hasInput = true;
      break;
    case OPT_INPUT:
      addFile(arg->getValue(), /*withLOption=*/false);
      hasInput = true;
      break;
    case OPT_defsym: {
      StringRef from;
      StringRef to;
      std::tie(from, to) = StringRef(arg->getValue()).split('=');
      if (from.empty() || to.empty())
        error("--defsym: syntax error: " + StringRef(arg->getValue()));
      else
        readDefsym(from, MemoryBufferRef(to, "--defsym"));
      break;
    }
    case OPT_script:
      if (std::optional<std::string> path = searchScript(arg->getValue())) {
        if (std::optional<MemoryBufferRef> mb = readFile(*path))
          readLinkerScript(*mb);
        break;
      }
      error(Twine("cannot find linker script ") + arg->getValue());
      break;
    case OPT_as_needed:
      config->asNeeded = true;
      break;
    case OPT_format:
      config->formatBinary = isFormatBinary(arg->getValue());
      break;
    case OPT_no_as_needed:
      config->asNeeded = false;
      break;
    case OPT_Bstatic:
    case OPT_omagic:
    case OPT_nmagic:
      config->isStatic = true;
      break;
    case OPT_Bdynamic:
      config->isStatic = false;
      break;
    case OPT_whole_archive:
      inWholeArchive = true;
      break;
    case OPT_no_whole_archive:
      inWholeArchive = false;
      break;
    case OPT_just_symbols:
      if (std::optional<MemoryBufferRef> mb = readFile(arg->getValue())) {
        files.push_back(createObjFile(*mb));
        files.back()->justSymbols = true;
      }
      break;
    case OPT_in_implib:
      if (armCmseImpLib)
        error("multiple CMSE import libraries not supported");
      else if (std::optional<MemoryBufferRef> mb = readFile(arg->getValue()))
        armCmseImpLib = createObjFile(*mb);
      break;
    case OPT_start_group:
      if (InputFile::isInGroup)
        error("nested --start-group");
      InputFile::isInGroup = true;
      break;
    case OPT_end_group:
      if (!InputFile::isInGroup)
        error("stray --end-group");
      InputFile::isInGroup = false;
      ++InputFile::nextGroupId;
      break;
    case OPT_start_lib:
      if (inLib)
        error("nested --start-lib");
      if (InputFile::isInGroup)
        error("may not nest --start-lib in --start-group");
      inLib = true;
      InputFile::isInGroup = true;
      break;
    case OPT_end_lib:
      if (!inLib)
        error("stray --end-lib");
      inLib = false;
      InputFile::isInGroup = false;
      ++InputFile::nextGroupId;
      break;
    case OPT_push_state:
      stack.emplace_back(config->asNeeded, config->isStatic, inWholeArchive);
      break;
    case OPT_pop_state:
      if (stack.empty()) {
        error("unbalanced --push-state/--pop-state");
        break;
      }
      std::tie(config->asNeeded, config->isStatic, inWholeArchive) = stack.back();
      stack.pop_back();
      break;
    }
  }

  if (files.empty() && !hasInput && errorCount() == 0)
    error("no input files");
}

// If -m <machine_type> was not given, infer it from object files.
void LinkerDriver::inferMachineType() {
  if (config->ekind != ELFNoneKind)
    return;

  for (InputFile *f : files) {
    if (f->ekind == ELFNoneKind)
      continue;
    config->ekind = f->ekind;
    config->emachine = f->emachine;
    config->osabi = f->osabi;
    config->mipsN32Abi = config->emachine == EM_MIPS && isMipsN32Abi(f);
    return;
  }
  error("target emulation unknown: -m or at least one .o file required");
}

// Parse -z max-page-size=<value>. The default value is defined by
// each target.
static uint64_t getMaxPageSize(opt::InputArgList &args) {
  uint64_t val = args::getZOptionValue(args, OPT_z, "max-page-size",
                                       target->defaultMaxPageSize);
  if (!isPowerOf2_64(val)) {
    error("max-page-size: value isn't a power of 2");
    return target->defaultMaxPageSize;
  }
  if (config->nmagic || config->omagic) {
    if (val != target->defaultMaxPageSize)
      warn("-z max-page-size set, but paging disabled by omagic or nmagic");
    return 1;
  }
  return val;
}

// Parse -z common-page-size=<value>. The default value is defined by
// each target.
static uint64_t getCommonPageSize(opt::InputArgList &args) {
  uint64_t val = args::getZOptionValue(args, OPT_z, "common-page-size",
                                       target->defaultCommonPageSize);
  if (!isPowerOf2_64(val)) {
    error("common-page-size: value isn't a power of 2");
    return target->defaultCommonPageSize;
  }
  if (config->nmagic || config->omagic) {
    if (val != target->defaultCommonPageSize)
      warn("-z common-page-size set, but paging disabled by omagic or nmagic");
    return 1;
  }
  // commonPageSize can't be larger than maxPageSize.
  if (val > config->maxPageSize)
    val = config->maxPageSize;
  return val;
}

// Parses --image-base option.
static std::optional<uint64_t> getImageBase(opt::InputArgList &args) {
  // Because we are using "Config->maxPageSize" here, this function has to be
  // called after the variable is initialized.
  auto *arg = args.getLastArg(OPT_image_base);
  if (!arg)
    return std::nullopt;

  StringRef s = arg->getValue();
  uint64_t v;
  if (!to_integer(s, v)) {
    error("--image-base: number expected, but got " + s);
    return 0;
  }
  if ((v % config->maxPageSize) != 0)
    warn("--image-base: address isn't multiple of page size: " + s);
  return v;
}

// Parses `--exclude-libs=lib,lib,...`.
// The library names may be delimited by commas or colons.
static DenseSet<StringRef> getExcludeLibs(opt::InputArgList &args) {
  DenseSet<StringRef> ret;
  for (auto *arg : args.filtered(OPT_exclude_libs)) {
    StringRef s = arg->getValue();
    for (;;) {
      size_t pos = s.find_first_of(",:");
      if (pos == StringRef::npos)
        break;
      ret.insert(s.substr(0, pos));
      s = s.substr(pos + 1);
    }
    ret.insert(s);
  }
  return ret;
}

// Handles the --exclude-libs option. If a static library file is specified
// by the --exclude-libs option, all public symbols from the archive become
// private unless otherwise specified by version scripts or something.
// A special library name "ALL" means all archive files.
//
// This is not a popular option, but some programs such as bionic libc use it.
static void excludeLibs(opt::InputArgList &args) {
  DenseSet<StringRef> libs = getExcludeLibs(args);
  bool all = libs.count("ALL");

  auto visit = [&](InputFile *file) {
    if (file->archiveName.empty() ||
        !(all || libs.count(path::filename(file->archiveName))))
      return;
    ArrayRef<Symbol *> symbols = file->getSymbols();
    if (isa<ELFFileBase>(file))
      symbols = cast<ELFFileBase>(file)->getGlobalSymbols();
    for (Symbol *sym : symbols)
      if (!sym->isUndefined() && sym->file == file)
        sym->versionId = VER_NDX_LOCAL;
  };

  for (ELFFileBase *file : ctx.objectFiles)
    visit(file);

  for (BitcodeFile *file : ctx.bitcodeFiles)
    visit(file);
}

// Force Sym to be entered in the output.
static void handleUndefined(Symbol *sym, const char *option) {
  // Since a symbol may not be used inside the program, LTO may
  // eliminate it. Mark the symbol as "used" to prevent it.
  sym->isUsedInRegularObj = true;

  if (!sym->isLazy())
    return;
  sym->extract();
  if (!config->whyExtract.empty())
    ctx.whyExtractRecords.emplace_back(option, sym->file, *sym);
}

// As an extension to GNU linkers, lld supports a variant of `-u`
// which accepts wildcard patterns. All symbols that match a given
// pattern are handled as if they were given by `-u`.
static void handleUndefinedGlob(StringRef arg) {
  Expected<GlobPattern> pat = GlobPattern::create(arg);
  if (!pat) {
    error("--undefined-glob: " + toString(pat.takeError()));
    return;
  }

  // Calling sym->extract() in the loop is not safe because it may add new
  // symbols to the symbol table, invalidating the current iterator.
  SmallVector<Symbol *, 0> syms;
  for (Symbol *sym : symtab.getSymbols())
    if (!sym->isPlaceholder() && pat->match(sym->getName()))
      syms.push_back(sym);

  for (Symbol *sym : syms)
    handleUndefined(sym, "--undefined-glob");
}

static void handleLibcall(StringRef name) {
  Symbol *sym = symtab.find(name);
  if (!sym || !sym->isLazy())
    return;

  MemoryBufferRef mb;
  mb = cast<LazyObject>(sym)->file->mb;

  if (isBitcode(mb))
    sym->extract();
}

static void writeArchiveStats() {
  if (config->printArchiveStats.empty())
    return;

  std::error_code ec;
  raw_fd_ostream os = ctx.openAuxiliaryFile(config->printArchiveStats, ec);
  if (ec) {
    error("--print-archive-stats=: cannot open " + config->printArchiveStats +
          ": " + ec.message());
    return;
  }

  os << "members\textracted\tarchive\n";

  SmallVector<StringRef, 0> archives;
  DenseMap<CachedHashStringRef, unsigned> all, extracted;
  for (ELFFileBase *file : ctx.objectFiles)
    if (file->archiveName.size())
      ++extracted[CachedHashStringRef(file->archiveName)];
  for (BitcodeFile *file : ctx.bitcodeFiles)
    if (file->archiveName.size())
      ++extracted[CachedHashStringRef(file->archiveName)];
  for (std::pair<StringRef, unsigned> f : ctx.driver.archiveFiles) {
    unsigned &v = extracted[CachedHashString(f.first)];
    os << f.second << '\t' << v << '\t' << f.first << '\n';
    // If the archive occurs multiple times, other instances have a count of 0.
    v = 0;
  }
}

static void writeWhyExtract() {
  if (config->whyExtract.empty())
    return;

  std::error_code ec;
  raw_fd_ostream os = ctx.openAuxiliaryFile(config->whyExtract, ec);
  if (ec) {
    error("cannot open --why-extract= file " + config->whyExtract + ": " +
          ec.message());
    return;
  }

  os << "reference\textracted\tsymbol\n";
  for (auto &entry : ctx.whyExtractRecords) {
    os << std::get<0>(entry) << '\t' << toString(std::get<1>(entry)) << '\t'
       << toString(std::get<2>(entry)) << '\n';
  }
}

static void reportBackrefs() {
  for (auto &ref : ctx.backwardReferences) {
    const Symbol &sym = *ref.first;
    std::string to = toString(ref.second.second);
    // Some libraries have known problems and can cause noise. Filter them out
    // with --warn-backrefs-exclude=. The value may look like (for --start-lib)
    // *.o or (archive member) *.a(*.o).
    bool exclude = false;
    for (const llvm::GlobPattern &pat : config->warnBackrefsExclude)
      if (pat.match(to)) {
        exclude = true;
        break;
      }
    if (!exclude)
      warn("backward reference detected: " + sym.getName() + " in " +
           toString(ref.second.first) + " refers to " + to);
  }
}

// Handle --dependency-file=<path>. If that option is given, lld creates a
// file at a given path with the following contents:
//
//   <output-file>: <input-file> ...
//
//   <input-file>:
//
// where <output-file> is a pathname of an output file and <input-file>
// ... is a list of pathnames of all input files. `make` command can read a
// file in the above format and interpret it as a dependency info. We write
// phony targets for every <input-file> to avoid an error when that file is
// removed.
//
// This option is useful if you want to make your final executable to depend
// on all input files including system libraries. Here is why.
//
// When you write a Makefile, you usually write it so that the final
// executable depends on all user-generated object files. Normally, you
// don't make your executable to depend on system libraries (such as libc)
// because you don't know the exact paths of libraries, even though system
// libraries that are linked to your executable statically are technically a
// part of your program. By using --dependency-file option, you can make
// lld to dump dependency info so that you can maintain exact dependencies
// easily.
static void writeDependencyFile() {
  std::error_code ec;
  raw_fd_ostream os = ctx.openAuxiliaryFile(config->dependencyFile, ec);
  if (ec) {
    error("cannot open " + config->dependencyFile + ": " + ec.message());
    return;
  }

  // We use the same escape rules as Clang/GCC which are accepted by Make/Ninja:
  // * A space is escaped by a backslash which itself must be escaped.
  // * A hash sign is escaped by a single backslash.
  // * $ is escapes as $$.
  auto printFilename = [](raw_fd_ostream &os, StringRef filename) {
    llvm::SmallString<256> nativePath;
    llvm::sys::path::native(filename.str(), nativePath);
    llvm::sys::path::remove_dots(nativePath, /*remove_dot_dot=*/true);
    for (unsigned i = 0, e = nativePath.size(); i != e; ++i) {
      if (nativePath[i] == '#') {
        os << '\\';
      } else if (nativePath[i] == ' ') {
        os << '\\';
        unsigned j = i;
        while (j > 0 && nativePath[--j] == '\\')
          os << '\\';
      } else if (nativePath[i] == '$') {
        os << '$';
      }
      os << nativePath[i];
    }
  };

  os << config->outputFile << ":";
  for (StringRef path : config->dependencyFiles) {
    os << " \\\n ";
    printFilename(os, path);
  }
  os << "\n";

  for (StringRef path : config->dependencyFiles) {
    os << "\n";
    printFilename(os, path);
    os << ":\n";
  }
}

// Replaces common symbols with defined symbols reside in .bss sections.
// This function is called after all symbol names are resolved. As a
// result, the passes after the symbol resolution won't see any
// symbols of type CommonSymbol.
static void replaceCommonSymbols() {
  llvm::TimeTraceScope timeScope("Replace common symbols");
  for (ELFFileBase *file : ctx.objectFiles) {
    if (!file->hasCommonSyms)
      continue;
    for (Symbol *sym : file->getGlobalSymbols()) {
      auto *s = dyn_cast<CommonSymbol>(sym);
      if (!s)
        continue;

      auto *bss = make<BssSection>("COMMON", s->size, s->alignment);
      bss->file = s->file;
      ctx.inputSections.push_back(bss);
      Defined(s->file, StringRef(), s->binding, s->stOther, s->type,
              /*value=*/0, s->size, bss)
          .overwrite(*s);
    }
  }
}

// If all references to a DSO happen to be weak, the DSO is not added to
// DT_NEEDED. If that happens, replace ShardSymbol with Undefined to avoid
// dangling references to an unneeded DSO. Use a weak binding to avoid
// --no-allow-shlib-undefined diagnostics. Similarly, demote lazy symbols.
static void demoteSharedAndLazySymbols() {
  llvm::TimeTraceScope timeScope("Demote shared and lazy symbols");
  for (Symbol *sym : symtab.getSymbols()) {
    auto *s = dyn_cast<SharedSymbol>(sym);
    if (!(s && !cast<SharedFile>(s->file)->isNeeded) && !sym->isLazy())
      continue;

    uint8_t binding = sym->isLazy() ? sym->binding : uint8_t(STB_WEAK);
    Undefined(nullptr, sym->getName(), binding, sym->stOther, sym->type)
        .overwrite(*sym);
    sym->versionId = VER_NDX_GLOBAL;
  }
}

// The section referred to by `s` is considered address-significant. Set the
// keepUnique flag on the section if appropriate.
static void markAddrsig(Symbol *s) {
  if (auto *d = dyn_cast_or_null<Defined>(s))
    if (d->section)
      // We don't need to keep text sections unique under --icf=all even if they
      // are address-significant.
      if (config->icf == ICFLevel::Safe || !(d->section->flags & SHF_EXECINSTR))
        d->section->keepUnique = true;
}

// Record sections that define symbols mentioned in --keep-unique <symbol>
// and symbols referred to by address-significance tables. These sections are
// ineligible for ICF.
template <class ELFT>
static void findKeepUniqueSections(opt::InputArgList &args) {
  for (auto *arg : args.filtered(OPT_keep_unique)) {
    StringRef name = arg->getValue();
    auto *d = dyn_cast_or_null<Defined>(symtab.find(name));
    if (!d || !d->section) {
      warn("could not find symbol " + name + " to keep unique");
      continue;
    }
    d->section->keepUnique = true;
  }

  // --icf=all --ignore-data-address-equality means that we can ignore
  // the dynsym and address-significance tables entirely.
  if (config->icf == ICFLevel::All && config->ignoreDataAddressEquality)
    return;

  // Symbols in the dynsym could be address-significant in other executables
  // or DSOs, so we conservatively mark them as address-significant.
  for (Symbol *sym : symtab.getSymbols())
    if (sym->includeInDynsym())
      markAddrsig(sym);

  // Visit the address-significance table in each object file and mark each
  // referenced symbol as address-significant.
  for (InputFile *f : ctx.objectFiles) {
    auto *obj = cast<ObjFile<ELFT>>(f);
    ArrayRef<Symbol *> syms = obj->getSymbols();
    if (obj->addrsigSec) {
      ArrayRef<uint8_t> contents =
          check(obj->getObj().getSectionContents(*obj->addrsigSec));
      const uint8_t *cur = contents.begin();
      while (cur != contents.end()) {
        unsigned size;
        const char *err;
        uint64_t symIndex = decodeULEB128(cur, &size, contents.end(), &err);
        if (err)
          fatal(toString(f) + ": could not decode addrsig section: " + err);
        markAddrsig(syms[symIndex]);
        cur += size;
      }
    } else {
      // If an object file does not have an address-significance table,
      // conservatively mark all of its symbols as address-significant.
      for (Symbol *s : syms)
        markAddrsig(s);
    }
  }
}

// This function reads a symbol partition specification section. These sections
// are used to control which partition a symbol is allocated to. See
// https://lld.llvm.org/Partitions.html for more details on partitions.
template <typename ELFT>
static void readSymbolPartitionSection(InputSectionBase *s) {
  // Read the relocation that refers to the partition's entry point symbol.
  Symbol *sym;
  const RelsOrRelas<ELFT> rels = s->template relsOrRelas<ELFT>();
  if (rels.areRelocsRel())
    sym = &s->getFile<ELFT>()->getRelocTargetSym(rels.rels[0]);
  else
    sym = &s->getFile<ELFT>()->getRelocTargetSym(rels.relas[0]);
  if (!isa<Defined>(sym) || !sym->includeInDynsym())
    return;

  StringRef partName = reinterpret_cast<const char *>(s->content().data());
  for (Partition &part : partitions) {
    if (part.name == partName) {
      sym->partition = part.getNumber();
      return;
    }
  }

  // Forbid partitions from being used on incompatible targets, and forbid them
  // from being used together with various linker features that assume a single
  // set of output sections.
  if (script->hasSectionsCommand)
    error(toString(s->file) +
          ": partitions cannot be used with the SECTIONS command");
  if (script->hasPhdrsCommands())
    error(toString(s->file) +
          ": partitions cannot be used with the PHDRS command");
  if (!config->sectionStartMap.empty())
    error(toString(s->file) + ": partitions cannot be used with "
                              "--section-start, -Ttext, -Tdata or -Tbss");
  if (config->emachine == EM_MIPS)
    error(toString(s->file) + ": partitions cannot be used on this target");

  // Impose a limit of no more than 254 partitions. This limit comes from the
  // sizes of the Partition fields in InputSectionBase and Symbol, as well as
  // the amount of space devoted to the partition number in RankFlags.
  if (partitions.size() == 254)
    fatal("may not have more than 254 partitions");

  partitions.emplace_back();
  Partition &newPart = partitions.back();
  newPart.name = partName;
  sym->partition = newPart.getNumber();
}

static Symbol *addUnusedUndefined(StringRef name,
                                  uint8_t binding = STB_GLOBAL) {
  return symtab.addSymbol(Undefined{nullptr, name, binding, STV_DEFAULT, 0});
}

static void markBuffersAsDontNeed(bool skipLinkedOutput) {
  // With --thinlto-index-only, all buffers are nearly unused from now on
  // (except symbol/section names used by infrequent passes). Mark input file
  // buffers as MADV_DONTNEED so that these pages can be reused by the expensive
  // thin link, saving memory.
  if (skipLinkedOutput) {
    for (MemoryBuffer &mb : llvm::make_pointee_range(ctx.memoryBuffers))
      mb.dontNeedIfMmap();
    return;
  }

  // Otherwise, just mark MemoryBuffers backing BitcodeFiles.
  DenseSet<const char *> bufs;
  for (BitcodeFile *file : ctx.bitcodeFiles)
    bufs.insert(file->mb.getBufferStart());
  for (BitcodeFile *file : ctx.lazyBitcodeFiles)
    bufs.insert(file->mb.getBufferStart());
  for (MemoryBuffer &mb : llvm::make_pointee_range(ctx.memoryBuffers))
    if (bufs.count(mb.getBufferStart()))
      mb.dontNeedIfMmap();
}

// This function is where all the optimizations of link-time
// optimization takes place. When LTO is in use, some input files are
// not in native object file format but in the LLVM bitcode format.
// This function compiles bitcode files into a few big native files
// using LLVM functions and replaces bitcode symbols with the results.
// Because all bitcode files that the program consists of are passed to
// the compiler at once, it can do a whole-program optimization.
template <class ELFT>
void LinkerDriver::compileBitcodeFiles(bool skipLinkedOutput) {
  llvm::TimeTraceScope timeScope("LTO");
  // Compile bitcode files and replace bitcode symbols.
  lto.reset(new BitcodeCompiler);
  for (BitcodeFile *file : ctx.bitcodeFiles)
    lto->add(*file);

  if (!ctx.bitcodeFiles.empty())
    markBuffersAsDontNeed(skipLinkedOutput);

  for (InputFile *file : lto->compile()) {
    auto *obj = cast<ObjFile<ELFT>>(file);
    obj->parse(/*ignoreComdats=*/true);

    // Parse '@' in symbol names for non-relocatable output.
    if (!config->relocatable)
      for (Symbol *sym : obj->getGlobalSymbols())
        if (sym->hasVersionSuffix)
          sym->parseSymbolVersion();
    ctx.objectFiles.push_back(obj);
  }
}

// The --wrap option is a feature to rename symbols so that you can write
// wrappers for existing functions. If you pass `--wrap=foo`, all
// occurrences of symbol `foo` are resolved to `__wrap_foo` (so, you are
// expected to write `__wrap_foo` function as a wrapper). The original
// symbol becomes accessible as `__real_foo`, so you can call that from your
// wrapper.
//
// This data structure is instantiated for each --wrap option.
struct WrappedSymbol {
  Symbol *sym;
  Symbol *real;
  Symbol *wrap;
};

// Handles --wrap option.
//
// This function instantiates wrapper symbols. At this point, they seem
// like they are not being used at all, so we explicitly set some flags so
// that LTO won't eliminate them.
static std::vector<WrappedSymbol> addWrappedSymbols(opt::InputArgList &args) {
  std::vector<WrappedSymbol> v;
  DenseSet<StringRef> seen;

  for (auto *arg : args.filtered(OPT_wrap)) {
    StringRef name = arg->getValue();
    if (!seen.insert(name).second)
      continue;

    Symbol *sym = symtab.find(name);
    if (!sym)
      continue;

    Symbol *wrap =
        addUnusedUndefined(saver().save("__wrap_" + name), sym->binding);

    // If __real_ is referenced, pull in the symbol if it is lazy. Do this after
    // processing __wrap_ as that may have referenced __real_.
    StringRef realName = saver().save("__real_" + name);
    if (symtab.find(realName))
      addUnusedUndefined(name, sym->binding);

    Symbol *real = addUnusedUndefined(realName);
    v.push_back({sym, real, wrap});

    // We want to tell LTO not to inline symbols to be overwritten
    // because LTO doesn't know the final symbol contents after renaming.
    real->scriptDefined = true;
    sym->scriptDefined = true;

    // If a symbol is referenced in any object file, bitcode file or shared
    // object, mark its redirection target (foo for __real_foo and __wrap_foo
    // for foo) as referenced after redirection, which will be used to tell LTO
    // to not eliminate the redirection target. If the object file defining the
    // symbol also references it, we cannot easily distinguish the case from
    // cases where the symbol is not referenced. Retain the redirection target
    // in this case because we choose to wrap symbol references regardless of
    // whether the symbol is defined
    // (https://sourceware.org/bugzilla/show_bug.cgi?id=26358).
    if (real->referenced || real->isDefined())
      sym->referencedAfterWrap = true;
    if (sym->referenced || sym->isDefined())
      wrap->referencedAfterWrap = true;
  }
  return v;
}

static void combineVersionedSymbol(Symbol &sym,
                                   DenseMap<Symbol *, Symbol *> &map) {
  const char *suffix1 = sym.getVersionSuffix();
  if (suffix1[0] != '@' || suffix1[1] == '@')
    return;

  // Check the existing symbol foo. We have two special cases to handle:
  //
  // * There is a definition of foo@v1 and foo@@v1.
  // * There is a definition of foo@v1 and foo.
  Defined *sym2 = dyn_cast_or_null<Defined>(symtab.find(sym.getName()));
  if (!sym2)
    return;
  const char *suffix2 = sym2->getVersionSuffix();
  if (suffix2[0] == '@' && suffix2[1] == '@' &&
      strcmp(suffix1 + 1, suffix2 + 2) == 0) {
    // foo@v1 and foo@@v1 should be merged, so redirect foo@v1 to foo@@v1.
    map.try_emplace(&sym, sym2);
    // If both foo@v1 and foo@@v1 are defined and non-weak, report a
    // duplicate definition error.
    if (sym.isDefined()) {
      sym2->checkDuplicate(cast<Defined>(sym));
      sym2->resolve(cast<Defined>(sym));
    } else if (sym.isUndefined()) {
      sym2->resolve(cast<Undefined>(sym));
    } else {
      sym2->resolve(cast<SharedSymbol>(sym));
    }
    // Eliminate foo@v1 from the symbol table.
    sym.symbolKind = Symbol::PlaceholderKind;
    sym.isUsedInRegularObj = false;
  } else if (auto *sym1 = dyn_cast<Defined>(&sym)) {
    if (sym2->versionId > VER_NDX_GLOBAL
            ? config->versionDefinitions[sym2->versionId].name == suffix1 + 1
            : sym1->section == sym2->section && sym1->value == sym2->value) {
      // Due to an assembler design flaw, if foo is defined, .symver foo,
      // foo@v1 defines both foo and foo@v1. Unless foo is bound to a
      // different version, GNU ld makes foo@v1 canonical and eliminates
      // foo. Emulate its behavior, otherwise we would have foo or foo@@v1
      // beside foo@v1. foo@v1 and foo combining does not apply if they are
      // not defined in the same place.
      map.try_emplace(sym2, &sym);
      sym2->symbolKind = Symbol::PlaceholderKind;
      sym2->isUsedInRegularObj = false;
    }
  }
}

// Do renaming for --wrap and foo@v1 by updating pointers to symbols.
//
// When this function is executed, only InputFiles and symbol table
// contain pointers to symbol objects. We visit them to replace pointers,
// so that wrapped symbols are swapped as instructed by the command line.
static void redirectSymbols(ArrayRef<WrappedSymbol> wrapped) {
  llvm::TimeTraceScope timeScope("Redirect symbols");
  DenseMap<Symbol *, Symbol *> map;
  for (const WrappedSymbol &w : wrapped) {
    map[w.sym] = w.wrap;
    map[w.real] = w.sym;
  }

  // If there are version definitions (versionDefinitions.size() > 2), enumerate
  // symbols with a non-default version (foo@v1) and check whether it should be
  // combined with foo or foo@@v1.
  if (config->versionDefinitions.size() > 2)
    for (Symbol *sym : symtab.getSymbols())
      if (sym->hasVersionSuffix)
        combineVersionedSymbol(*sym, map);

  if (map.empty())
    return;

  // Update pointers in input files.
  parallelForEach(ctx.objectFiles, [&](ELFFileBase *file) {
    for (Symbol *&sym : file->getMutableGlobalSymbols())
      if (Symbol *s = map.lookup(sym))
        sym = s;
  });

  // Update pointers in the symbol table.
  for (const WrappedSymbol &w : wrapped)
    symtab.wrap(w.sym, w.real, w.wrap);
}

static void checkAndReportMissingFeature(StringRef config, uint32_t features,
                                         uint32_t mask, const Twine &report) {
  if (!(features & mask)) {
    if (config == "error")
      error(report);
    else if (config == "warning")
      warn(report);
  }
}

// To enable CET (x86's hardware-assisted control flow enforcement), each
// source file must be compiled with -fcf-protection. Object files compiled
// with the flag contain feature flags indicating that they are compatible
// with CET. We enable the feature only when all object files are compatible
// with CET.
//
// This is also the case with AARCH64's BTI and PAC which use the similar
// GNU_PROPERTY_AARCH64_FEATURE_1_AND mechanism.
static uint32_t getAndFeatures() {
  if (config->emachine != EM_386 && config->emachine != EM_X86_64 &&
      config->emachine != EM_AARCH64)
    return 0;

  uint32_t ret = -1;
  for (ELFFileBase *f : ctx.objectFiles) {
    uint32_t features = f->andFeatures;

    checkAndReportMissingFeature(
        config->zBtiReport, features, GNU_PROPERTY_AARCH64_FEATURE_1_BTI,
        toString(f) + ": -z bti-report: file does not have "
                      "GNU_PROPERTY_AARCH64_FEATURE_1_BTI property");

    checkAndReportMissingFeature(
        config->zCetReport, features, GNU_PROPERTY_X86_FEATURE_1_IBT,
        toString(f) + ": -z cet-report: file does not have "
                      "GNU_PROPERTY_X86_FEATURE_1_IBT property");

    checkAndReportMissingFeature(
        config->zCetReport, features, GNU_PROPERTY_X86_FEATURE_1_SHSTK,
        toString(f) + ": -z cet-report: file does not have "
                      "GNU_PROPERTY_X86_FEATURE_1_SHSTK property");

    if (config->zForceBti && !(features & GNU_PROPERTY_AARCH64_FEATURE_1_BTI)) {
      features |= GNU_PROPERTY_AARCH64_FEATURE_1_BTI;
      if (config->zBtiReport == "none")
        warn(toString(f) + ": -z force-bti: file does not have "
                           "GNU_PROPERTY_AARCH64_FEATURE_1_BTI property");
    } else if (config->zForceIbt &&
               !(features & GNU_PROPERTY_X86_FEATURE_1_IBT)) {
      if (config->zCetReport == "none")
        warn(toString(f) + ": -z force-ibt: file does not have "
                           "GNU_PROPERTY_X86_FEATURE_1_IBT property");
      features |= GNU_PROPERTY_X86_FEATURE_1_IBT;
    }
    if (config->zPacPlt && !(features & GNU_PROPERTY_AARCH64_FEATURE_1_PAC)) {
      warn(toString(f) + ": -z pac-plt: file does not have "
                         "GNU_PROPERTY_AARCH64_FEATURE_1_PAC property");
      features |= GNU_PROPERTY_AARCH64_FEATURE_1_PAC;
    }
    ret &= features;
  }

  // Force enable Shadow Stack.
  if (config->zShstk)
    ret |= GNU_PROPERTY_X86_FEATURE_1_SHSTK;

  return ret;
}

static void initSectionsAndLocalSyms(ELFFileBase *file, bool ignoreComdats) {
  switch (file->ekind) {
  case ELF32LEKind:
    cast<ObjFile<ELF32LE>>(file)->initSectionsAndLocalSyms(ignoreComdats);
    break;
  case ELF32BEKind:
    cast<ObjFile<ELF32BE>>(file)->initSectionsAndLocalSyms(ignoreComdats);
    break;
  case ELF64LEKind:
    cast<ObjFile<ELF64LE>>(file)->initSectionsAndLocalSyms(ignoreComdats);
    break;
  case ELF64BEKind:
    cast<ObjFile<ELF64BE>>(file)->initSectionsAndLocalSyms(ignoreComdats);
    break;
  default:
    llvm_unreachable("");
  }
}

static void postParseObjectFile(ELFFileBase *file) {
  switch (file->ekind) {
  case ELF32LEKind:
    cast<ObjFile<ELF32LE>>(file)->postParse();
    break;
  case ELF32BEKind:
    cast<ObjFile<ELF32BE>>(file)->postParse();
    break;
  case ELF64LEKind:
    cast<ObjFile<ELF64LE>>(file)->postParse();
    break;
  case ELF64BEKind:
    cast<ObjFile<ELF64BE>>(file)->postParse();
    break;
  default:
    llvm_unreachable("");
  }
}

namespace {
enum class RISCVFunctionSplitBlockReason {
  UnsupportedSection,
  ComdatOrGroup,
  LinkOrder,
  NoFunctionRanges,
  ZeroSizedOnly,
  FunctionRangeOverflow,
  OverlappingFunctions,
  SymbolRangeCrossesPiece,
  SourceRelocationUnowned,
  SourceSectionSymbol,
  SourceAddendCrossesPiece,
  IncomingSectionSymbol,
  IncomingAddendCrossesPiece,
  IncomingEhFrame,
  IncomingDebugRelocation,
  CallPairCrossesFunction,
  PcrelPairCrossesFunction,
  AlignCrossesFunction,
  NoRelocCrossFunctionJal,
  NoRelocCrossFunctionBranch,
  FunctionFallthrough,
  ComputedJump,
  UnsupportedRvcControlFlow,
  UnexplainedGap,
  Count,
};

//static StringRef toString(RISCVFunctionSplitBlockReason r) {
static StringRef blockReasonToString(RISCVFunctionSplitBlockReason r) {
  switch (r) {
  case RISCVFunctionSplitBlockReason::UnsupportedSection:
    return "unsupported-section";
  case RISCVFunctionSplitBlockReason::ComdatOrGroup:
    return "comdat-or-group";
  case RISCVFunctionSplitBlockReason::LinkOrder:
    return "link-order";
  case RISCVFunctionSplitBlockReason::NoFunctionRanges:
    return "no-function-ranges";
  case RISCVFunctionSplitBlockReason::ZeroSizedOnly:
    return "zero-sized-only";
  case RISCVFunctionSplitBlockReason::FunctionRangeOverflow:
    return "function-range-overflow";
  case RISCVFunctionSplitBlockReason::OverlappingFunctions:
    return "overlapping-functions";
  case RISCVFunctionSplitBlockReason::SymbolRangeCrossesPiece:
    return "symbol-range-crosses-piece";
  case RISCVFunctionSplitBlockReason::SourceRelocationUnowned:
    return "source-relocation-unowned";
  case RISCVFunctionSplitBlockReason::SourceSectionSymbol:
    return "source-section-symbol";
  case RISCVFunctionSplitBlockReason::SourceAddendCrossesPiece:
    return "source-addend-crosses-piece";
  case RISCVFunctionSplitBlockReason::IncomingSectionSymbol:
    return "incoming-section-symbol";
  case RISCVFunctionSplitBlockReason::IncomingAddendCrossesPiece:
    return "incoming-addend-crosses-piece";
  case RISCVFunctionSplitBlockReason::IncomingEhFrame:
    return "incoming-eh-frame";
  case RISCVFunctionSplitBlockReason::IncomingDebugRelocation:
    return "incoming-debug-relocation";
  case RISCVFunctionSplitBlockReason::CallPairCrossesFunction:
    return "call-pair-crosses-function";
  case RISCVFunctionSplitBlockReason::PcrelPairCrossesFunction:
    return "pcrel-pair-crosses-function";
  case RISCVFunctionSplitBlockReason::AlignCrossesFunction:
    return "align-crosses-function";
  case RISCVFunctionSplitBlockReason::NoRelocCrossFunctionJal:
    return "no-reloc-cross-function-jal";
  case RISCVFunctionSplitBlockReason::NoRelocCrossFunctionBranch:
    return "no-reloc-cross-function-branch";
  case RISCVFunctionSplitBlockReason::FunctionFallthrough:
    return "function-fallthrough";
  case RISCVFunctionSplitBlockReason::ComputedJump:
    return "computed-jump";
  case RISCVFunctionSplitBlockReason::UnsupportedRvcControlFlow:
    return "unsupported-rvc-control-flow";
  case RISCVFunctionSplitBlockReason::UnexplainedGap:
    return "unexplained-gap";
  case RISCVFunctionSplitBlockReason::Count:
    break;
  }
  llvm_unreachable("invalid RISC-V function split block reason");
}

struct RISCVFunctionRange {
  uint64_t begin;
  uint64_t end;
};

enum class RISCVFunctionSplitDebugFallbackReason {
  AllocSource,
  NonDebugSource,
  EhFrame,
  NonDefinedTarget,
  SectionSymbol,
  OtherSection,
  UnsupportedRel,
  TargetGap,
  TargetOutOfRange,
  AmbiguousBoundary,
  AddendCrossesChild,
  InconsistentSymbolMapping,
  Count,
};

static StringRef debugFallbackReasonToString(
    RISCVFunctionSplitDebugFallbackReason r) {
  switch (r) {
  case RISCVFunctionSplitDebugFallbackReason::AllocSource:
    return "alloc-source";
  case RISCVFunctionSplitDebugFallbackReason::NonDebugSource:
    return "non-debug-source";
  case RISCVFunctionSplitDebugFallbackReason::EhFrame:
    return "eh-frame";
  case RISCVFunctionSplitDebugFallbackReason::NonDefinedTarget:
    return "non-defined-target";
  case RISCVFunctionSplitDebugFallbackReason::SectionSymbol:
    return "section-symbol";
  case RISCVFunctionSplitDebugFallbackReason::OtherSection:
    return "other-section";
  case RISCVFunctionSplitDebugFallbackReason::UnsupportedRel:
    return "unsupported-rel";
  case RISCVFunctionSplitDebugFallbackReason::TargetGap:
    return "target-gap";
  case RISCVFunctionSplitDebugFallbackReason::TargetOutOfRange:
    return "target-out-of-range";
  case RISCVFunctionSplitDebugFallbackReason::AmbiguousBoundary:
    return "ambiguous-boundary";
  case RISCVFunctionSplitDebugFallbackReason::AddendCrossesChild:
    return "addend-crosses-child";
  case RISCVFunctionSplitDebugFallbackReason::InconsistentSymbolMapping:
    return "inconsistent-symbol-mapping";
  case RISCVFunctionSplitDebugFallbackReason::Count:
    break;
  }
  llvm_unreachable("invalid RISC-V function split debug fallback reason");
}

struct RISCVDebugRelocMapping {
  InputSectionBase *source = nullptr;
  Defined *target = nullptr;
  uint64_t parentOffset = 0;
  uint32_t childIndex = 0;
  uint64_t symbolValue = 0;
  uint64_t targetLocalOffset = 0;
  bool parentEnd = false;
  bool boundaryStart = false;
};

struct RISCVIncomingRelocAudit {
  std::string sourceFile;
  std::string sourceSection;
  uint32_t sourceSectionType = 0;
  uint64_t sourceSectionFlags = 0;
  uint64_t sourceOffset = 0;
  bool sourceAlloc = false;
  bool sourceDebug = false;
  bool sourceEhFrame = false;
  RelType relocType = static_cast<RelType>(0);
  std::string targetSymbol;
  uint8_t targetSymbolType = STT_NOTYPE;
  bool targetSectionSymbol = false;
  int64_t addend = 0;
  bool hasTargetOffset = false;
  uint64_t targetOffset = 0;
  bool uniquelyMappable = false;
  bool targetGap = false;
  bool targetBoundary = false;
  uint64_t childLocalOffset = 0;
};

struct RISCVFunctionSplitAuditResult {
  InputSection *parent = nullptr;
  SmallVector<RISCVFunctionRange, 0> ranges;
  uint64_t executableBytes = 0;
  uint64_t candidateFunctionBytes = 0;
  uint64_t gapBytes = 0;
  uint32_t functionCount = 0;
  uint32_t sourceRelocationCount = 0;
  uint32_t incomingRelocationCount = 0;
  uint32_t zeroSizeFunctionCount = 0;
  bool safe = true;
  std::bitset<static_cast<size_t>(RISCVFunctionSplitBlockReason::Count)>
      reasons;
  SmallVector<RISCVIncomingRelocAudit, 0> incomingRelocs;
  SmallVector<RISCVDebugRelocMapping, 0> debugRelocMappings;
  std::bitset<
      static_cast<size_t>(RISCVFunctionSplitDebugFallbackReason::Count)>
      debugFallbackReasons;
  std::array<uint32_t,
             static_cast<size_t>(RISCVFunctionSplitDebugFallbackReason::Count)>
      debugFallbackRelocCounts = {};
};

struct RISCVFunctionSplitDetail {
  InputSection *parent = nullptr;
  SmallVector<RISCVFunctionRange, 0> ranges;
  SmallVector<SmallVector<uint64_t, 0>, 0> childRelocOffsets;
  uint32_t relocationCount = 0;
};

struct RISCVFunctionSplitStats {
  uint32_t splitParentCount = 0;
  uint32_t skippedSafeSingleFunctionParentCount = 0;
  uint32_t createdChildCount = 0;
  uint32_t symbolRebindCount = 0;
  uint32_t relocationRepartitionCount = 0;
  uint32_t parentFallbackCount = 0;
  uint64_t splitBytes = 0;
  SmallVector<RISCVFunctionSplitDetail, 0> details;
};

static void addReason(RISCVFunctionSplitAuditResult &r,
                      RISCVFunctionSplitBlockReason reason) {
  r.safe = false;
  r.reasons.set(static_cast<size_t>(reason));
}

static bool hasReason(const RISCVFunctionSplitAuditResult &r,
                      RISCVFunctionSplitBlockReason reason) {
  return r.reasons.test(static_cast<size_t>(reason));
}

static void addDebugFallback(
    RISCVFunctionSplitAuditResult &r,
    RISCVFunctionSplitDebugFallbackReason reason) {
  r.debugFallbackReasons.set(static_cast<size_t>(reason));
  ++r.debugFallbackRelocCounts[static_cast<size_t>(reason)];
}

static bool addDebugRelocMapping(RISCVFunctionSplitAuditResult &result,
                                 InputSectionBase &from, Defined &d,
                                 uint64_t parentOffset, uint32_t childIndex,
                                 uint64_t symbolValue,
                                 uint64_t targetLocalOffset, bool parentEnd,
                                 bool boundaryStart) {
  for (const RISCVDebugRelocMapping &m : result.debugRelocMappings)
    if (m.target == &d &&
        (m.childIndex != childIndex || m.symbolValue != symbolValue ||
         m.parentEnd != parentEnd || m.boundaryStart != boundaryStart)) {
      addDebugFallback(
          result,
          RISCVFunctionSplitDebugFallbackReason::InconsistentSymbolMapping);
      return false;
    }
  result.debugRelocMappings.push_back({&from, &d, parentOffset, childIndex,
                                       symbolValue, targetLocalOffset,
                                       parentEnd, boundaryStart});
  return true;
}

static int functionRangeStartIndex(ArrayRef<RISCVFunctionRange> ranges,
                                   uint64_t off) {
  for (auto [i, r] : llvm::enumerate(ranges))
    if (r.begin == off)
      return static_cast<int>(i);
  return -1;
}

static bool isDebugBoundaryStartSymbol(Defined &d,
                                       ArrayRef<RISCVFunctionRange> ranges,
                                       uint64_t parentSize) {
  return d.type == STT_NOTYPE && d.size == 0 && !d.isSection() &&
         d.value != parentSize &&
         functionRangeStartIndex(ranges, d.value) != -1;
}

static int rangeIndex(ArrayRef<RISCVFunctionRange> ranges, uint64_t off) {
  auto it = llvm::partition_point(
      ranges, [=](const RISCVFunctionRange &r) { return r.end <= off; });
  if (it != ranges.end() && it->begin <= off && off < it->end)
    return it - ranges.begin();
  return -1;
}

static bool rangeInOnePiece(ArrayRef<RISCVFunctionRange> ranges, uint64_t begin,
                            uint64_t end) {
  if (begin > end)
    return false;
  if (begin == end)
    return rangeIndex(ranges, begin) != -1;
  int i = rangeIndex(ranges, begin);
  return i != -1 && end <= ranges[i].end;
}

static bool isRISCVFunctionSplitBoundary(ArrayRef<RISCVFunctionRange> ranges,
                                         uint64_t off) {
  for (size_t i = 1, e = ranges.size(); i != e; ++i)
    if (ranges[i].begin == off)
      return true;
  return !ranges.empty() && ranges.back().end == off;
}

static bool hasRISCVFunctionRangeStart(ArrayRef<RISCVFunctionRange> ranges,
                                       uint64_t off) {
  return llvm::any_of(
      ranges, [=](const RISCVFunctionRange &r) { return r.begin == off; });
}

static bool isAllZero(ArrayRef<uint8_t> data) {
  return llvm::all_of(data, [](uint8_t b) { return b == 0; });
}

static bool isRISCVNopPadding(ArrayRef<uint8_t> data) {
  for (size_t i = 0, e = data.size(); i != e;) {
    if (i + 4 <= e && llvm::support::endian::read32le(data.data() + i) == 0x00000013) {
      i += 4;
      continue;
    }
    if (i + 2 <= e && llvm::support::endian::read16le(data.data() + i) == 0x0001) {
      i += 2;
      continue;
    }
    return false;
  }
  return true;
}

static uint32_t bits(uint32_t v, unsigned hi, unsigned lo) {
  return (v >> lo) & ((1u << (hi - lo + 1)) - 1);
}

static int64_t decodeJal(uint32_t insn) {
  uint32_t imm = ((insn >> 31) << 20) | (bits(insn, 19, 12) << 12) |
                 (bits(insn, 20, 20) << 11) | (bits(insn, 30, 21) << 1);
  return SignExtend64<21>(imm);
}

static int64_t decodeBranch(uint32_t insn) {
  uint32_t imm = ((insn >> 31) << 12) | (bits(insn, 7, 7) << 11) |
                 (bits(insn, 30, 25) << 5) | (bits(insn, 11, 8) << 1);
  return SignExtend64<13>(imm);
}

static int64_t decodeCJ(uint16_t insn) {
  uint32_t imm = (bits(insn, 12, 12) << 11) | (bits(insn, 8, 8) << 10) |
                 (bits(insn, 10, 9) << 8) | (bits(insn, 6, 6) << 7) |
                 (bits(insn, 7, 7) << 6) | (bits(insn, 2, 2) << 5) |
                 (bits(insn, 11, 11) << 4) | (bits(insn, 5, 3) << 1);
  return SignExtend64<12>(imm);
}

static int64_t decodeCB(uint16_t insn) {
  uint32_t imm = (bits(insn, 12, 12) << 8) | (bits(insn, 6, 5) << 6) |
                 (bits(insn, 2, 2) << 5) | (bits(insn, 11, 10) << 3) |
                 (bits(insn, 4, 3) << 1);
  return SignExtend64<9>(imm);
}

static bool hasRelocType(const DenseMap<uint64_t, SmallVector<RelType, 0>> &rels,
                         uint64_t off, ArrayRef<RelType> types) {
  auto it = rels.find(off);
  if (it == rels.end())
    return false;
  ArrayRef<RelType> got = it->second;
  return llvm::any_of(types, [&](RelType type) {
    return llvm::is_contained(got, type);
  });
}

enum class RISCVDirectRelocKind {
  Jal,
  Branch,
  RvcJump,
  RvcBranch,
};

static bool hasDirectReloc(
    const DenseMap<uint64_t, SmallVector<RelType, 0>> &rels, uint64_t off,
    RISCVDirectRelocKind kind) {
  switch (kind) {
  case RISCVDirectRelocKind::Jal:
    return hasRelocType(rels, off, {R_RISCV_JAL});
  case RISCVDirectRelocKind::Branch:
    return hasRelocType(rels, off, {R_RISCV_BRANCH});
  case RISCVDirectRelocKind::RvcJump:
    return hasRelocType(rels, off, {R_RISCV_RVC_JUMP});
  case RISCVDirectRelocKind::RvcBranch:
    return hasRelocType(rels, off, {R_RISCV_RVC_BRANCH});
  }
  llvm_unreachable("invalid RISC-V direct relocation kind");
}

static bool checkedAddend(uint64_t value, int64_t addend, uint64_t &result) {
  if (addend >= 0) {
    uint64_t u = static_cast<uint64_t>(addend);
    if (value > std::numeric_limits<uint64_t>::max() - u)
      return false;
    result = value + u;
    return true;
  }
  uint64_t magnitude =
      addend == std::numeric_limits<int64_t>::min()
          ? (uint64_t{1} << 63)
          : static_cast<uint64_t>(-addend);
  if (value < magnitude)
    return false;
  result = value - magnitude;
  return true;
}

static void checkDirectTarget(
    ArrayRef<RISCVFunctionRange> ranges,
    const DenseMap<uint64_t, SmallVector<RelType, 0>> &typesAtOffset,
    RISCVFunctionSplitAuditResult &result, uint64_t off, int64_t target,
    RISCVDirectRelocKind kind) {
  bool branch = kind == RISCVDirectRelocKind::Branch ||
                kind == RISCVDirectRelocKind::RvcBranch;
  if (target < 0) {
    if (!hasDirectReloc(typesAtOffset, off, kind))
      addReason(result, branch ? RISCVFunctionSplitBlockReason::
                                    NoRelocCrossFunctionBranch
                              : RISCVFunctionSplitBlockReason::
                                    NoRelocCrossFunctionJal);
    return;
  }
  int sourceFunc = rangeIndex(ranges, off);
  int targetFunc = rangeIndex(ranges, static_cast<uint64_t>(target));
  if ((sourceFunc == -1 || targetFunc == -1 || sourceFunc != targetFunc) &&
      !hasDirectReloc(typesAtOffset, off, kind))
    addReason(result, branch ? RISCVFunctionSplitBlockReason::
                                  NoRelocCrossFunctionBranch
                            : RISCVFunctionSplitBlockReason::
                                  NoRelocCrossFunctionJal);
}

template <class RelTy>
static int64_t getRISCVFunctionSplitAddend(const RelTy &rel) {
  if constexpr (RelTy::IsRela)
    return rel.r_addend;
  return 0;
}

template <class RelTy>
static void recordIncomingRelocAudit(InputSection &parent,
                                     ArrayRef<RISCVFunctionRange> ranges,
                                     InputSectionBase &from, const RelTy &rel,
                                     Defined &d,
                                     RISCVFunctionSplitAuditResult &result) {
  RISCVIncomingRelocAudit audit;
  audit.sourceFile = toString(from.file);
  audit.sourceSection = from.name.str();
  audit.sourceSectionType = from.type;
  audit.sourceSectionFlags = from.flags;
  audit.sourceOffset = rel.r_offset;
  audit.sourceAlloc = from.flags & SHF_ALLOC;
  audit.sourceDebug = isDebugSection(from);
  audit.sourceEhFrame = isa<EhInputSection>(&from);
  audit.relocType = rel.getType(config->isMips64EL);
  audit.targetSymbol = d.getName().str();
  audit.targetSymbolType = d.type;
  audit.targetSectionSymbol = d.isSection();
  audit.addend = getRISCVFunctionSplitAddend(rel);

  uint64_t target = d.value;
  bool hasTarget = true;
  if constexpr (RelTy::IsRela)
    hasTarget = checkedAddend(d.value, rel.r_addend, target);
  audit.hasTargetOffset = hasTarget;
  if (hasTarget) {
    audit.targetOffset = target;
    int piece = rangeIndex(ranges, target);
    audit.uniquelyMappable = piece != -1;
    if (audit.uniquelyMappable)
      audit.childLocalOffset = target - ranges[piece].begin;
    else
      audit.targetGap = target < parent.content().size();
    audit.targetBoundary = hasRISCVFunctionRangeStart(ranges, target) ||
                           isRISCVFunctionSplitBoundary(ranges, target);
  }
  result.incomingRelocs.push_back(std::move(audit));
}

template <class RelTy>
static bool planDebugIncomingReloc(InputSection &parent,
                                   ArrayRef<RISCVFunctionRange> ranges,
                                   InputSectionBase &from, const RelTy &rel,
                                   Defined *d,
                                   RISCVFunctionSplitAuditResult &result) {
  if (from.flags & SHF_ALLOC) {
    addDebugFallback(result,
                     RISCVFunctionSplitDebugFallbackReason::AllocSource);
    return false;
  }
  if (!isDebugSection(from)) {
    addDebugFallback(result,
                     RISCVFunctionSplitDebugFallbackReason::NonDebugSource);
    return false;
  }
  if (isa<EhInputSection>(&from)) {
    addDebugFallback(result, RISCVFunctionSplitDebugFallbackReason::EhFrame);
    return false;
  }
  if (!d) {
    addDebugFallback(
        result, RISCVFunctionSplitDebugFallbackReason::NonDefinedTarget);
    return false;
  }
  if (d->isSection()) {
    addDebugFallback(result,
                     RISCVFunctionSplitDebugFallbackReason::SectionSymbol);
    return false;
  }
  if (d->section != &parent) {
    addDebugFallback(result, RISCVFunctionSplitDebugFallbackReason::OtherSection);
    return false;
  }
  if constexpr (!RelTy::IsRela) {
    addDebugFallback(result,
                     RISCVFunctionSplitDebugFallbackReason::UnsupportedRel);
    return false;
  } else {
    uint64_t target;
    if (!checkedAddend(d->value, rel.r_addend, target)) {
      addDebugFallback(
          result, RISCVFunctionSplitDebugFallbackReason::TargetOutOfRange);
      return false;
    }
    uint64_t parentSize = parent.content().size();
    if (target > parentSize) {
      addDebugFallback(
          result, RISCVFunctionSplitDebugFallbackReason::TargetOutOfRange);
      return false;
    }

    if (target == parentSize) {
      if (d->value != parentSize || rel.r_addend != 0 || ranges.empty() ||
          ranges.back().end != parentSize) {
        addDebugFallback(result,
                         RISCVFunctionSplitDebugFallbackReason::TargetGap);
        return false;
      }
      uint64_t value = ranges.back().end - ranges.back().begin;
      return addDebugRelocMapping(
          result, from, *d, target, static_cast<uint32_t>(ranges.size() - 1),
          value, value, true, false);
    }

    int symbolPiece = rangeIndex(ranges, d->value);
    if (symbolPiece == -1) {
      addDebugFallback(result,
                       d->value < parentSize
                           ? RISCVFunctionSplitDebugFallbackReason::TargetGap
                           : RISCVFunctionSplitDebugFallbackReason::
                                 TargetOutOfRange);
      return false;
    }
    int targetPiece = rangeIndex(ranges, target);
    if (targetPiece == -1) {
      addDebugFallback(result,
                       target < parentSize
                           ? RISCVFunctionSplitDebugFallbackReason::TargetGap
                           : RISCVFunctionSplitDebugFallbackReason::
                                 TargetOutOfRange);
      return false;
    }
    int boundaryStart = -1;
    if (d->type == STT_NOTYPE && d->size == 0 && d->value != parentSize)
      boundaryStart = functionRangeStartIndex(ranges, d->value);

    if (boundaryStart != -1) {
      if (symbolPiece != boundaryStart) {
        addDebugFallback(
            result, RISCVFunctionSplitDebugFallbackReason::AmbiguousBoundary);
        return false;
      }
      if (symbolPiece != targetPiece) {
        addDebugFallback(
            result, RISCVFunctionSplitDebugFallbackReason::AddendCrossesChild);
        return false;
      }
      return addDebugRelocMapping(
          result, from, *d, target, static_cast<uint32_t>(boundaryStart), 0,
          target - ranges[targetPiece].begin, false, true);
    }

    if (d->size) {
      if (d->size > std::numeric_limits<uint64_t>::max() - d->value ||
          !rangeInOnePiece(ranges, d->value, d->value + d->size)) {
        addDebugFallback(
            result, RISCVFunctionSplitDebugFallbackReason::AmbiguousBoundary);
        return false;
      }
    } else if (isRISCVFunctionSplitBoundary(ranges, d->value) &&
               (d->type != STT_FUNC ||
                !hasRISCVFunctionRangeStart(ranges, d->value))) {
      addDebugFallback(
          result, RISCVFunctionSplitDebugFallbackReason::AmbiguousBoundary);
      return false;
    }

    if (symbolPiece != targetPiece) {
      addDebugFallback(
          result, RISCVFunctionSplitDebugFallbackReason::AddendCrossesChild);
      return false;
    }

    bool atBoundary = isRISCVFunctionSplitBoundary(ranges, target);
    bool isFunctionStart = hasRISCVFunctionRangeStart(ranges, target);
    if (atBoundary && target != 0 &&
        !(d->type == STT_FUNC && isFunctionStart)) {
      addDebugFallback(
          result, RISCVFunctionSplitDebugFallbackReason::AmbiguousBoundary);
      return false;
    }

    return addDebugRelocMapping(
        result, from, *d, target, static_cast<uint32_t>(symbolPiece),
        d->value - ranges[symbolPiece].begin,
        target - ranges[targetPiece].begin, false, false);
  }
}

template <class ELFT, class RelTy>
static void auditSourceRelocs(InputSection &sec,
                              ArrayRef<RISCVFunctionRange> ranges,
                              ArrayRef<RelTy> rels,
                              RISCVFunctionSplitAuditResult &result) {
  DenseMap<uint64_t, SmallVector<RelType, 0>> typesAtOffset;
  for (const RelTy &rel : rels) {
    ++result.sourceRelocationCount;
    RelType type = rel.getType(config->isMips64EL);
    uint64_t off = rel.r_offset;
    if (rangeIndex(ranges, off) == -1)
      addReason(result, RISCVFunctionSplitBlockReason::SourceRelocationUnowned);
    typesAtOffset[off].push_back(type);
  }

  for (const RelTy &rel : rels) {
    RelType type = rel.getType(config->isMips64EL);
    uint64_t off = rel.r_offset;
    int func = rangeIndex(ranges, off);
    Symbol &target = sec.getFile<ELFT>()->getRelocTargetSym(rel);
    if (auto *d = dyn_cast<Defined>(&target)) {
      if (d->section == &sec) {
        if (d->isSection()) {
          addReason(result, RISCVFunctionSplitBlockReason::SourceSectionSymbol);
        } else if constexpr (!RelTy::IsRela) {
          addReason(result,
                    RISCVFunctionSplitBlockReason::SourceAddendCrossesPiece);
        } else {
          uint64_t effectiveTarget;
          int symbolPiece = rangeIndex(ranges, d->value);
          bool ok = checkedAddend(d->value, rel.r_addend, effectiveTarget);
          int targetPiece = ok ? rangeIndex(ranges, effectiveTarget) : -1;
          if (!ok || symbolPiece == -1 || targetPiece == -1 ||
              symbolPiece != targetPiece ||
              (d->size &&
               !rangeInOnePiece(ranges, d->value, d->value + d->size)))
            addReason(
                result,
                RISCVFunctionSplitBlockReason::SourceAddendCrossesPiece);
        }
      }
    }
    if (type == R_RISCV_CALL || type == R_RISCV_CALL_PLT) {
      bool validCallPair = func != -1 && rangeInOnePiece(ranges, off, off + 8);
      if (validCallPair) {
        ArrayRef<uint8_t> data = sec.content();
        uint32_t auipc = llvm::support::endian::read32le(data.data() + off);
        uint32_t jalr = llvm::support::endian::read32le(data.data() + off + 4);
        uint32_t auipcRd = bits(auipc, 11, 7);
        uint32_t jalrRd = bits(jalr, 11, 7);
        uint32_t jalrRs1 = bits(jalr, 19, 15);
        validCallPair = (auipc & 0x7f) == 0x17 && auipcRd != 0 &&
                        (jalr & 0x7f) == 0x67 && jalrRs1 == auipcRd &&
                        (jalrRd == 0 || jalrRd == 1);
      }
      if (!validCallPair)
        addReason(result,
                  RISCVFunctionSplitBlockReason::CallPairCrossesFunction);
    }
    if (type == R_RISCV_ALIGN) {
      uint64_t end = off + getRISCVFunctionSplitAddend(rel);
      if (func == -1 || end > ranges[func].end)
        addReason(result,
                  RISCVFunctionSplitBlockReason::AlignCrossesFunction);
    }
    if (type == R_RISCV_PCREL_LO12_I || type == R_RISCV_PCREL_LO12_S) {
      Symbol &sym = sec.getFile<ELFT>()->getRelocTargetSym(rel);
      auto *d = dyn_cast<Defined>(&sym);
      if (!d || d->section != &sec) {
        addReason(result,
                  RISCVFunctionSplitBlockReason::PcrelPairCrossesFunction);
        continue;
      }
      int hiFunc = rangeIndex(ranges, d->value);
      if (func == -1 || hiFunc == -1 || func != hiFunc ||
          !hasRelocType(typesAtOffset, d->value,
                        {R_RISCV_PCREL_HI20, R_RISCV_GOT_HI20,
                         R_RISCV_TLS_GD_HI20, R_RISCV_TLS_GOT_HI20}))
        addReason(result,
                  RISCVFunctionSplitBlockReason::PcrelPairCrossesFunction);
    }
  }

  ArrayRef<uint8_t> data = sec.content();
  const bool rvc =
      sec.getFile<ELFT>()->getObj().getHeader().e_flags & EF_RISCV_RVC;
  for (const RISCVFunctionRange &r : ranges) {
    uint64_t off = r.begin;
    while (off < r.end) {
      if (off + 2 > data.size()) {
        addReason(result, RISCVFunctionSplitBlockReason::FunctionFallthrough);
        break;
      }
      uint16_t half = llvm::support::endian::read16le(data.data() + off);
      if ((half & 3) != 3) {
        if (!rvc)
          addReason(result,
                    RISCVFunctionSplitBlockReason::UnsupportedRvcControlFlow);
        uint16_t op = half & 3, funct3 = bits(half, 15, 13);
        bool terminal = false;
        bool branch = false;
        bool hasDirectTarget = false;
        RISCVDirectRelocKind relocKind = RISCVDirectRelocKind::RvcJump;
        int64_t target = 0;
        if (op == 1 && (funct3 == 5 || funct3 == 1)) {
          target = static_cast<int64_t>(off) + decodeCJ(half);
          hasDirectTarget = true;
          relocKind = RISCVDirectRelocKind::RvcJump;
          terminal = funct3 == 5; // c.j is terminal; c.jal returns.
        } else if (op == 1 && (funct3 == 6 || funct3 == 7)) {
          target = static_cast<int64_t>(off) + decodeCB(half);
          hasDirectTarget = true;
          relocKind = RISCVDirectRelocKind::RvcBranch;
          branch = true;
        } else if (op == 2 && funct3 == 4 && bits(half, 6, 2) == 0) {
          uint32_t rs1 = bits(half, 11, 7);
          bool link = bits(half, 12, 12);
          if (!link && rs1 == 1)
            terminal = true;
          else
            addReason(result, RISCVFunctionSplitBlockReason::ComputedJump);
        }
        if (hasDirectTarget)
          checkDirectTarget(ranges, typesAtOffset, result, off, target,
                            relocKind);
        if (branch && off + 2 == r.end)
          addReason(result, RISCVFunctionSplitBlockReason::FunctionFallthrough);
        if (!terminal && off + 2 == r.end)
          addReason(result, RISCVFunctionSplitBlockReason::FunctionFallthrough);
        off += 2;
        continue;
      }

      if (off + 4 > r.end) {
        addReason(result, RISCVFunctionSplitBlockReason::FunctionFallthrough);
        break;
      }
      uint32_t insn = llvm::support::endian::read32le(data.data() + off);
      uint32_t opcode = insn & 0x7f;
      bool terminal = false;
      if (opcode == 0x17 && off + 4 < r.end) {
        uint32_t next = llvm::support::endian::read32le(data.data() + off + 4);
        if ((next & 0x7f) == 0x67 &&
            (llvm::is_contained(typesAtOffset.lookup(off),
                                static_cast<RelType>(R_RISCV_CALL)) ||
             llvm::is_contained(typesAtOffset.lookup(off),
                                static_cast<RelType>(R_RISCV_CALL_PLT)))) {
          uint32_t auipcRd = bits(insn, 11, 7);
          uint32_t jalrRd = bits(next, 11, 7);
          uint32_t jalrRs1 = bits(next, 19, 15);
          if (auipcRd == 0 || jalrRs1 != auipcRd ||
              (jalrRd != 0 && jalrRd != 1))
            addReason(result,
                      RISCVFunctionSplitBlockReason::CallPairCrossesFunction);
          terminal = jalrRd == 0;
          if (!terminal && off + 8 == r.end)
            addReason(result,
                      RISCVFunctionSplitBlockReason::FunctionFallthrough);
          off += 8;
          continue;
        }
      }
      if (opcode == 0x6f) {
        int64_t target = static_cast<int64_t>(off) + decodeJal(insn);
        checkDirectTarget(ranges, typesAtOffset, result, off, target,
                          RISCVDirectRelocKind::Jal);
        terminal = bits(insn, 11, 7) == 0;
      } else if (opcode == 0x63) {
        int64_t target = static_cast<int64_t>(off) + decodeBranch(insn);
        checkDirectTarget(ranges, typesAtOffset, result, off, target,
                          RISCVDirectRelocKind::Branch);
        if (off + 4 == r.end)
          addReason(result, RISCVFunctionSplitBlockReason::FunctionFallthrough);
      } else if (opcode == 0x67) {
        uint32_t rd = bits(insn, 11, 7);
        uint32_t rs1 = bits(insn, 19, 15);
        int64_t imm = SignExtend64<12>(bits(insn, 31, 20));
        if (rd == 0 && rs1 == 1 && imm == 0)
          terminal = true;
        else
          addReason(result, RISCVFunctionSplitBlockReason::ComputedJump);
      }
      if (!terminal && off + 4 == r.end)
        addReason(result, RISCVFunctionSplitBlockReason::FunctionFallthrough);
      off += 4;
    }
  }
}

template <class ELFT, class RelTy>
static void auditIncomingRelocs(InputSection &parent,
                                ArrayRef<RISCVFunctionRange> ranges,
                                InputSectionBase &from, ArrayRef<RelTy> rels,
                                RISCVFunctionSplitAuditResult &result) {
  for (const RelTy &rel : rels) {
    Symbol &sym = from.getFile<ELFT>()->getRelocTargetSym(rel);
    auto *d = dyn_cast<Defined>(&sym);
    if (!d || d->section != &parent)
      continue;
    ++result.incomingRelocationCount;
    recordIncomingRelocAudit(parent, ranges, from, rel, *d, result);
    if (config->riscvFunctionSectionsSplitDebugRelocs &&
        from.name.starts_with(".debug") && (from.flags & SHF_ALLOC)) {
      addDebugFallback(result,
                       RISCVFunctionSplitDebugFallbackReason::AllocSource);
      addReason(result, RISCVFunctionSplitBlockReason::IncomingDebugRelocation);
      continue;
    }
    if (config->riscvFunctionSectionsSplitDebugRelocs &&
        isDebugBoundaryStartSymbol(*d, ranges, parent.content().size()) &&
        !isDebugSection(from)) {
      if (isa<EhInputSection>(&from))
        addDebugFallback(result, RISCVFunctionSplitDebugFallbackReason::EhFrame);
      else if (from.flags & SHF_ALLOC)
        addDebugFallback(result,
                         RISCVFunctionSplitDebugFallbackReason::AllocSource);
      else
        addDebugFallback(
            result, RISCVFunctionSplitDebugFallbackReason::NonDebugSource);
      addReason(result, RISCVFunctionSplitBlockReason::IncomingDebugRelocation);
      continue;
    }
    if (isa<EhInputSection>(&from)) {
      addReason(result, RISCVFunctionSplitBlockReason::IncomingEhFrame);
      continue;
    }
    if (isDebugSection(from)) {
      if (config->riscvFunctionSectionsSplitDebugRelocs &&
          planDebugIncomingReloc(parent, ranges, from, rel, d, result))
        continue;
      addReason(result,
                RISCVFunctionSplitBlockReason::IncomingDebugRelocation);
      continue;
    }
    if (d->isSection()) {
      addReason(result, RISCVFunctionSplitBlockReason::IncomingSectionSymbol);
      continue;
    }
    if constexpr (!RelTy::IsRela) {
      addReason(result,
                RISCVFunctionSplitBlockReason::IncomingAddendCrossesPiece);
      continue;
    } else {
      int64_t addend = rel.r_addend;
      uint64_t target;
      if (!checkedAddend(d->value, addend, target)) {
        addReason(result,
                  RISCVFunctionSplitBlockReason::IncomingAddendCrossesPiece);
        continue;
      }
      int symbolPiece = rangeIndex(ranges, d->value);
      int targetPiece = rangeIndex(ranges, target);
      if (symbolPiece == -1 || targetPiece == -1 ||
          symbolPiece != targetPiece ||
          (d->size && !rangeInOnePiece(ranges, d->value, d->value + d->size)))
        addReason(result,
                  RISCVFunctionSplitBlockReason::IncomingAddendCrossesPiece);
    }
  }
}

template <class ELFT>
static RISCVFunctionSplitAuditResult auditRISCVFunctionSplitSection(
    ObjFile<ELFT> &file, InputSection &sec) {
  RISCVFunctionSplitAuditResult result;
  result.parent = &sec;
  result.executableBytes = sec.content().size();
  if (sec.type != SHT_PROGBITS || !(sec.flags & SHF_ALLOC) ||
      !(sec.flags & SHF_EXECINSTR) || sec.name == ".eh_frame" ||
      (sec.flags & SHF_MERGE)) {
    addReason(result, RISCVFunctionSplitBlockReason::UnsupportedSection);
    return result;
  }
  if (sec.nextInSectionGroup) {
    addReason(result, RISCVFunctionSplitBlockReason::ComdatOrGroup);
    return result;
  }
  if (sec.flags & SHF_LINK_ORDER) {
    addReason(result, RISCVFunctionSplitBlockReason::LinkOrder);
    return result;
  }

  SmallVector<RISCVFunctionRange, 0> ranges;
  for (Symbol *sym : file.getSymbols()) {
    auto *d = dyn_cast_or_null<Defined>(sym);
    if (!d || d->section != &sec)
      continue;
    if (d->type == STT_FUNC && d->size == 0) {
      ++result.zeroSizeFunctionCount;
      continue;
    }
    if (d->type != STT_FUNC || d->size == 0)
      continue;
    if (d->value > sec.content().size() ||
        d->size > std::numeric_limits<uint64_t>::max() - d->value ||
        d->value + d->size > sec.content().size()) {
      addReason(result,
                RISCVFunctionSplitBlockReason::FunctionRangeOverflow);
      continue;
    }
    ranges.push_back({d->value, d->value + d->size});
  }
  if (ranges.empty()) {
    if (result.zeroSizeFunctionCount)
      addReason(result, RISCVFunctionSplitBlockReason::ZeroSizedOnly);
    else
      addReason(result, RISCVFunctionSplitBlockReason::NoFunctionRanges);
    return result;
  }

  llvm::sort(ranges, [](const RISCVFunctionRange &a,
                        const RISCVFunctionRange &b) {
    return std::tie(a.begin, a.end) < std::tie(b.begin, b.end);
  });
  SmallVector<RISCVFunctionRange, 0> unique;
  for (RISCVFunctionRange r : ranges) {
    if (!unique.empty() && r.begin == unique.back().begin &&
        r.end == unique.back().end)
      continue;
    if (!unique.empty() && r.begin < unique.back().end) {
      addReason(result, RISCVFunctionSplitBlockReason::OverlappingFunctions);
      continue;
    }
    unique.push_back(r);
    result.candidateFunctionBytes += r.end - r.begin;
  }
  ranges = std::move(unique);
  result.ranges = ranges;
  result.functionCount = ranges.size();

  uint64_t cursor = 0;
  for (RISCVFunctionRange r : ranges) {
    if (cursor < r.begin) {
      ArrayRef<uint8_t> gap = sec.content().slice(cursor, r.begin - cursor);
      result.gapBytes += gap.size();
      if (!isAllZero(gap) && !isRISCVNopPadding(gap))
        addReason(result, RISCVFunctionSplitBlockReason::UnexplainedGap);
    }
    cursor = r.end;
  }
  if (cursor < sec.content().size()) {
    ArrayRef<uint8_t> gap = sec.content().slice(cursor);
    result.gapBytes += gap.size();
    if (!isAllZero(gap) && !isRISCVNopPadding(gap))
      addReason(result, RISCVFunctionSplitBlockReason::UnexplainedGap);
  }

  for (Symbol *sym : file.getSymbols()) {
    auto *d = dyn_cast_or_null<Defined>(sym);
    if (!d || d->section != &sec || d->type == STT_FUNC || d->size == 0 ||
        d->isSection())
      continue;
    if (!rangeInOnePiece(ranges, d->value, d->value + d->size))
      addReason(result,
                RISCVFunctionSplitBlockReason::SymbolRangeCrossesPiece);
  }

  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  if (rels.areRelocsRel())
    auditSourceRelocs<ELFT>(sec, ranges, rels.rels, result);
  else
    auditSourceRelocs<ELFT>(sec, ranges, rels.relas, result);

  for (ELFFileBase *base : ctx.objectFiles) {
    auto *obj = dyn_cast<ObjFile<ELFT>>(base);
    if (!obj)
      continue;
    for (InputSectionBase *s : obj->getSections()) {
      if (!s || s == &InputSection::discarded || s == &sec)
        continue;
      RelsOrRelas<ELFT> rs = s->template relsOrRelas<ELFT>();
      if (rs.areRelocsRel())
        auditIncomingRelocs<ELFT>(sec, ranges, *s, rs.rels, result);
      else
        auditIncomingRelocs<ELFT>(sec, ranges, *s, rs.relas, result);
    }
  }
  return result;
}

template <class ELFT>
static bool splitRISCVFunctionSplitSection(
    const RISCVFunctionSplitAuditResult &plan, RISCVFunctionSplitStats &stats) {
  InputSection *parent = plan.parent;
  if (riscvFunctionSplitChildren.contains(parent))
    return false;
  if (parent->kind() != SectionBase::Regular)
    return false;

  RelsOrRelas<ELFT> rels = parent->template relsOrRelas<ELFT>();
  if (rels.areRelocsRel())
    return false;

  struct SymbolRebind {
    Defined *sym = nullptr;
    uint32_t childIndex = 0;
    uint64_t value = 0;
  };
  SmallVector<SymbolRebind, 0> rebindings;
  auto findDebugMapping = [&](Defined *d) -> const RISCVDebugRelocMapping * {
    for (const RISCVDebugRelocMapping &m : plan.debugRelocMappings)
      if (m.target == d)
        return &m;
    return nullptr;
  };
  auto *file = cast<ObjFile<ELFT>>(parent->file);
  for (Symbol *sym : file->getSymbols()) {
    auto *d = dyn_cast_or_null<Defined>(sym);
    if (!d || d->section != parent || d->isSection())
      continue;

    int i = rangeIndex(plan.ranges, d->value);
    if (i == -1) {
      if (const RISCVDebugRelocMapping *m = findDebugMapping(d);
          m && m->parentEnd) {
        rebindings.push_back({d, m->childIndex, m->symbolValue});
        continue;
      }
      return false;
    }
    if (d->size) {
      if (d->size > std::numeric_limits<uint64_t>::max() - d->value ||
          !rangeInOnePiece(plan.ranges, d->value, d->value + d->size))
        return false;
    } else if (isRISCVFunctionSplitBoundary(plan.ranges, d->value) &&
               (d->type != STT_FUNC ||
                !hasRISCVFunctionRangeStart(plan.ranges, d->value))) {
      if (const RISCVDebugRelocMapping *m = findDebugMapping(d);
          m && m->boundaryStart) {
        rebindings.push_back({d, m->childIndex, m->symbolValue});
        continue;
      }
      return false;
    }
    rebindings.push_back(
        {d, static_cast<uint32_t>(i), d->value - plan.ranges[i].begin});
  }

  using Elf_Rela = typename ELFT::Rela;
  SmallVector<SmallVector<Elf_Rela, 0>, 0> partitionedRelas;
  partitionedRelas.resize(plan.ranges.size());
  for (const Elf_Rela &rel : rels.relas) {
    int i = rangeIndex(plan.ranges, rel.r_offset);
    if (i == -1)
      return false;
    Elf_Rela copy = rel;
    copy.r_offset -= plan.ranges[i].begin;
    partitionedRelas[i].push_back(copy);
  }

  SmallVector<InputSection *, 0> children;
  children.reserve(plan.ranges.size());
  ArrayRef<uint8_t> parentContent = parent->content();
  for (auto [i, r] : llvm::enumerate(plan.ranges)) {
    ArrayRef<uint8_t> data =
        parentContent.slice(r.begin, static_cast<size_t>(r.end - r.begin));
    auto *child = makeThreadLocal<InputSection>(
        parent->file, parent->flags, parent->type,
        i == 0 ? parent->addralign : 1, data, parent->name);
    child->entsize = parent->entsize;
    child->link = parent->link;
    child->info = parent->info;
    child->relSecIdx = parent->relSecIdx;
    child->keepUnique = !config->riscvFunctionSectionsSplitICF;
    RISCVFunctionSplitRelocStorage storage;
    storage.relocsAreRela = true;
    storage.relocCount = static_cast<uint32_t>(partitionedRelas[i].size());
    storage.parent = parent;
    storage.originalBegin = r.begin;
    storage.originalEnd = r.end;
    if (!partitionedRelas[i].empty()) {
      auto *buf = makeThreadLocalN<Elf_Rela>(partitionedRelas[i].size());
      llvm::copy(partitionedRelas[i], buf);
      storage.relocs = buf;
    }
    riscvFunctionSplitRelocStorage[child] = storage;
    children.push_back(child);
  }

  if (!config->riscvFunctionSectionsSplitGC)
    for (size_t i = 0, e = children.size(); i != e; ++i)
      children[i]->nextInSectionGroup = children[(i + 1) % e];

  for (SymbolRebind r : rebindings) {
    r.sym->section = children[r.childIndex];
    r.sym->value = r.value;
  }

  SmallVector<InputSectionBase *, 0> childBases;
  for (InputSection *child : children)
    childBases.push_back(child);
  riscvFunctionSplitChildren[parent] = std::move(childBases);
  ++stats.splitParentCount;
  stats.createdChildCount += static_cast<uint32_t>(children.size());
  stats.splitBytes += parent->content().size();
  stats.symbolRebindCount += static_cast<uint32_t>(rebindings.size());
  stats.relocationRepartitionCount += static_cast<uint32_t>(rels.relas.size());
  SmallVector<SmallVector<uint64_t, 0>, 0> childRelocOffsets;
  childRelocOffsets.resize(partitionedRelas.size());
  for (size_t i = 0, e = partitionedRelas.size(); i != e; ++i)
    for (const Elf_Rela &rel : partitionedRelas[i])
      childRelocOffsets[i].push_back(rel.r_offset);
  stats.details.push_back({parent, plan.ranges, std::move(childRelocOffsets),
                           static_cast<uint32_t>(rels.relas.size())});
  return true;
}

template <class ELFT>
static RISCVFunctionSplitStats
splitRISCVFunctionSections(ArrayRef<RISCVFunctionSplitAuditResult> results) {
  RISCVFunctionSplitStats stats;
  riscvFunctionSplitChildren.clear();
  riscvFunctionSplitRelocStorage.clear();

  for (const RISCVFunctionSplitAuditResult &r : results) {
    if (!r.safe)
      continue;
    if (r.ranges.size() <= 1) {
      if (r.ranges.size() == 1)
        ++stats.skippedSafeSingleFunctionParentCount;
      continue;
    }
    if (r.gapBytes != 0 || script->hasSectionsCommand || config->emitRelocs ||
        config->copyRelocs || config->gdbIndex) {
      ++stats.parentFallbackCount;
      continue;
    }
    if (!splitRISCVFunctionSplitSection<ELFT>(r, stats))
      ++stats.parentFallbackCount;
  }

  return stats;
}

static bool hasAcceptedDebugReloc(const RISCVFunctionSplitAuditResult &r) {
  return !r.debugRelocMappings.empty();
}

static void printRISCVFunctionSplitDebugRelocStats(
    ArrayRef<RISCVFunctionSplitAuditResult> results,
    const RISCVFunctionSplitStats &splitStats) {
  if (!config->riscvFunctionSectionsSplitDebugRelocs)
    return;

  uint64_t accepted = 0, interior = 0, parentEnd = 0;
  uint64_t planned = 0, plannedBoundaryStart = 0, rejectedAmbiguous = 0;
  uint32_t newlySafeParents = 0, newlySplitParents = 0;
  uint64_t newlySplitFunctions = 0, newlySplitBytes = 0;
  uint32_t fallbackParents = 0;
  SmallVector<Defined *, 0> reboundTargets;
  std::array<uint32_t,
             static_cast<size_t>(RISCVFunctionSplitDebugFallbackReason::Count)>
      fallbackCounts = {};

  for (const RISCVFunctionSplitAuditResult &r : results) {
    planned += r.debugRelocMappings.size();
    for (const RISCVDebugRelocMapping &m : r.debugRelocMappings)
      if (m.boundaryStart)
        ++plannedBoundaryStart;
    rejectedAmbiguous +=
        r.debugFallbackRelocCounts[static_cast<size_t>(
            RISCVFunctionSplitDebugFallbackReason::AmbiguousBoundary)];

    if (r.safe && hasAcceptedDebugReloc(r)) {
      accepted += r.debugRelocMappings.size();
      for (const RISCVDebugRelocMapping &m : r.debugRelocMappings) {
        if (m.parentEnd)
          ++parentEnd;
        else
          ++interior;
        if (!llvm::is_contained(reboundTargets, m.target))
          reboundTargets.push_back(m.target);
      }
      if (r.safe)
        ++newlySafeParents;
    }

    if (!r.safe) {
      bool hasFallback = false;
      for (size_t i = 0; i != fallbackCounts.size(); ++i)
        if (r.debugFallbackReasons.test(i)) {
          ++fallbackCounts[i];
          hasFallback = true;
        }
      if (hasFallback)
        ++fallbackParents;
    }
  }

  for (const RISCVFunctionSplitDetail &d : splitStats.details) {
    auto it = llvm::find_if(results, [&](const RISCVFunctionSplitAuditResult &r) {
      return r.parent == d.parent;
    });
    if (it == results.end() || !hasAcceptedDebugReloc(*it))
      continue;
    ++newlySplitParents;
    newlySplitFunctions += d.ranges.size();
    newlySplitBytes += d.parent->content().size();
  }

  message(Twine("riscv-function-sections-split: phase2b-debug: accepted debug relocation count: ") +
          Twine(accepted));
  message(Twine("riscv-function-sections-split: phase2b-debug: planned debug relocation count: ") +
          Twine(planned));
  message(Twine("riscv-function-sections-split: phase2b-debug: accepted interior relocation count: ") +
          Twine(interior));
  message(Twine("riscv-function-sections-split: phase2b-debug: planned boundary-start relocation count: ") +
          Twine(plannedBoundaryStart));
  message(Twine("riscv-function-sections-split: phase2b-debug: accepted parent-end relocation count: ") +
          Twine(parentEnd));
  message(Twine("riscv-function-sections-split: phase2b-debug: rejected ambiguous-boundary relocation count: ") +
          Twine(rejectedAmbiguous));
  message(Twine("riscv-function-sections-split: phase2b-debug: rebound target symbol count: ") +
          Twine(reboundTargets.size()));
  message(Twine("riscv-function-sections-split: phase2b-debug: newly safe parent count: ") +
          Twine(newlySafeParents));
  message(Twine("riscv-function-sections-split: phase2b-debug: newly split parent count: ") +
          Twine(newlySplitParents));
  message(Twine("riscv-function-sections-split: phase2b-debug: newly split function count: ") +
          Twine(newlySplitFunctions));
  message(Twine("riscv-function-sections-split: phase2b-debug: newly split bytes: ") +
          Twine(newlySplitBytes));
  message(Twine("riscv-function-sections-split: phase2b-debug: fallback parent count: ") +
          Twine(fallbackParents));

  SmallVector<std::pair<std::string, uint32_t>, 0> fallbackStats;
  for (size_t i = 0; i != fallbackCounts.size(); ++i)
    if (fallbackCounts[i])
      fallbackStats.push_back(
          {debugFallbackReasonToString(
               static_cast<RISCVFunctionSplitDebugFallbackReason>(i))
               .str(),
           fallbackCounts[i]});
  llvm::sort(fallbackStats, [](const auto &a, const auto &b) {
    return a.first < b.first;
  });
  for (const auto &it : fallbackStats)
    message(Twine("riscv-function-sections-split: phase2b-debug: fallback: ") +
            it.first + ": parents " + Twine(it.second));

  SmallVector<const RISCVFunctionSplitAuditResult *, 0> debugParents;
  for (const RISCVFunctionSplitAuditResult &r : results)
    if (!r.safe &&
        (!r.debugRelocMappings.empty() || r.debugFallbackReasons.any()))
      debugParents.push_back(&r);
  llvm::sort(debugParents, [](const RISCVFunctionSplitAuditResult *a,
                              const RISCVFunctionSplitAuditResult *b) {
    std::string af = toString(a->parent->file);
    std::string bf = toString(b->parent->file);
    if (af != bf)
      return af < bf;
    return a->parent->name < b->parent->name;
  });
  for (const RISCVFunctionSplitAuditResult *r : debugParents) {
    uint32_t boundary = 0, parentEndRelocs = 0;
    for (const RISCVDebugRelocMapping &m : r->debugRelocMappings) {
      if (m.boundaryStart)
        ++boundary;
      if (m.parentEnd)
        ++parentEndRelocs;
    }
    uint32_t rejected = 0;
    SmallVector<std::string, 0> fallbacks;
    for (size_t i = 0; i != r->debugFallbackRelocCounts.size(); ++i)
      if (r->debugFallbackRelocCounts[i]) {
        rejected += r->debugFallbackRelocCounts[i];
        fallbacks.push_back(
            debugFallbackReasonToString(
                static_cast<RISCVFunctionSplitDebugFallbackReason>(i))
                .str());
      }
    llvm::sort(fallbacks);
    message(Twine("riscv-function-sections-split: phase2b-debug: parent: ") +
            toString(r->parent->file) + ":(" + r->parent->name +
            ") planned relocations: " + Twine(r->debugRelocMappings.size()) +
            " boundary-start relocations: " + Twine(boundary) +
            " parent-end relocations: " + Twine(parentEndRelocs) +
            " rejected relocations: " + Twine(rejected) + " fallbacks: " +
            (fallbacks.empty() ? Twine("none")
                               : Twine(llvm::join(fallbacks, ","))));
  }
}

template <class ELFT> static void auditRISCVFunctionSectionsSplit() {
  riscvFunctionSplitChildren.clear();
  riscvFunctionSplitRelocStorage.clear();
  riscvRelocOverrideStorage.clear();
  if (!config->riscvFunctionSectionsSplit || config->emachine != EM_RISCV ||
      config->is64 || config->relocatable)
    return;

  SmallVector<RISCVFunctionSplitAuditResult, 0> results;
  for (ELFFileBase *base : ctx.objectFiles) {
    auto *file = dyn_cast<ObjFile<ELFT>>(base);
    if (!file)
      continue;
    for (InputSectionBase *s : file->getSections()) {
      auto *isec = dyn_cast_or_null<InputSection>(s);
      if (!isec || isec == &InputSection::discarded)
        continue;
      if (!(isec->flags & SHF_EXECINSTR))
        continue;
      RISCVFunctionSplitAuditResult r =
          auditRISCVFunctionSplitSection<ELFT>(*file, *isec);
      if (!hasReason(r, RISCVFunctionSplitBlockReason::UnsupportedSection))
        results.push_back(r);
    }
  }

  RISCVFunctionSplitStats splitStats =
      splitRISCVFunctionSections<ELFT>(results);

  if (!config->printRISCVFunctionSectionsSplit)
    return;

  uint64_t safeBytes = 0, candidateBytes = 0, functionRanges = 0;
  uint32_t safeParents = 0, unsafeParents = 0;
  std::array<uint32_t,
             static_cast<size_t>(RISCVFunctionSplitBlockReason::Count)>
      reasonCounts = {};

  for (const RISCVFunctionSplitAuditResult &r : results) {
    message(Twine("riscv-function-sections-split: parent section: ") +
            r.parent->name);
    message(Twine("riscv-function-sections-split: object file: ") +
            toString(r.parent->file));
    message(Twine("riscv-function-sections-split: section size: ") +
            Twine(r.executableBytes));
    message(Twine("riscv-function-sections-split: unique function range count: ") +
            Twine(r.functionCount));
    message(Twine("riscv-function-sections-split: candidate function bytes: ") +
            Twine(r.candidateFunctionBytes));
    message(Twine("riscv-function-sections-split: gap bytes: ") +
            Twine(r.gapBytes));
    message(Twine("riscv-function-sections-split: incoming relocation count: ") +
            Twine(r.incomingRelocationCount));
    message(Twine("riscv-function-sections-split: source relocation count: ") +
            Twine(r.sourceRelocationCount));
    message(Twine("riscv-function-sections-split: status: ") +
            StringRef(r.safe ? "safe" : "unsafe"));
    SmallVector<StringRef, 0> reasons;
    for (size_t i = 0; i != static_cast<size_t>(
                              RISCVFunctionSplitBlockReason::Count);
         ++i)
      if (r.reasons.test(i))
        reasons.push_back(blockReasonToString(
            static_cast<RISCVFunctionSplitBlockReason>(i)));
    llvm::sort(reasons);
    if (reasons.empty())
      message("riscv-function-sections-split: block reasons: none");
    else
      message(Twine("riscv-function-sections-split: block reasons: ") +
              llvm::join(reasons.begin(), reasons.end(), ","));
    candidateBytes += r.candidateFunctionBytes;
    functionRanges += r.functionCount;
    if (r.safe) {
      ++safeParents;
      safeBytes += r.candidateFunctionBytes;
    } else {
      ++unsafeParents;
      for (size_t i = 0; i != reasonCounts.size(); ++i)
        if (r.reasons.test(i))
          ++reasonCounts[i];
    }
  }
  message(Twine("riscv-function-sections-split: summary: candidate parents: ") +
          Twine(results.size()));
  message(Twine("riscv-function-sections-split: summary: safe parents: ") +
          Twine(safeParents));
  message(Twine("riscv-function-sections-split: summary: unsafe parents: ") +
          Twine(unsafeParents));
  message(Twine("riscv-function-sections-split: summary: unique function ranges: ") +
          Twine(functionRanges));
  message(Twine("riscv-function-sections-split: summary: candidate bytes: ") +
          Twine(candidateBytes));
  message(Twine("riscv-function-sections-split: summary: safe bytes: ") +
          Twine(safeBytes));
  for (size_t i = 0; i != reasonCounts.size(); ++i)
    if (reasonCounts[i])
      message(Twine("riscv-function-sections-split: summary: ") +
              blockReasonToString(static_cast<RISCVFunctionSplitBlockReason>(i)) + ": " +
              Twine(reasonCounts[i]));
  message(Twine("riscv-function-sections-split: phase1a: split parent count: ") +
          Twine(splitStats.splitParentCount));
  message(Twine("riscv-function-sections-split: phase1a: skipped safe single-function parent count: ") +
          Twine(splitStats.skippedSafeSingleFunctionParentCount));
  message(Twine("riscv-function-sections-split: phase1a: created child count: ") +
          Twine(splitStats.createdChildCount));
  message(Twine("riscv-function-sections-split: phase1a: split bytes: ") +
          Twine(splitStats.splitBytes));
  message(Twine("riscv-function-sections-split: phase1a: symbol rebind count: ") +
          Twine(splitStats.symbolRebindCount));
  message(Twine("riscv-function-sections-split: phase1a: relocation repartition count: ") +
          Twine(splitStats.relocationRepartitionCount));
  message(Twine("riscv-function-sections-split: phase1a: parent fallback count: ") +
          Twine(splitStats.parentFallbackCount));
  for (const RISCVFunctionSplitDetail &d : splitStats.details) {
    message(Twine("riscv-function-sections-split: phase1a: split parent: ") +
            toString(d.parent->file) + ":(" + d.parent->name + ") size " +
            Twine(d.parent->content().size()) + " children " +
            Twine(d.ranges.size()) + " relocs " + Twine(d.relocationCount));
    for (auto [i, r] : llvm::enumerate(d.ranges)) {
      message(Twine("riscv-function-sections-split: phase1a: child range: [") +
              Twine(r.begin) + "," + Twine(r.end) + ")");
      SmallVector<std::string, 0> offsets;
      for (uint64_t off : d.childRelocOffsets[i])
        offsets.push_back(Twine(off).str());
      std::string offsetList =
          offsets.empty() ? std::string("none") : llvm::join(offsets, ",");
      message(Twine("riscv-function-sections-split: phase1a: child relocation offsets: ") +
              offsetList);
    }
  }
  printRISCVFunctionSplitDebugRelocStats(results, splitStats);
}

static void printRISCVFunctionSplitGCStats() {
  if (!config->riscvFunctionSectionsSplitGC ||
      !config->printRISCVFunctionSectionsSplit)
    return;

  uint32_t independentChildCount = 0, liveChildCount = 0, deadChildCount = 0;
  uint64_t liveChildBytes = 0, deadChildBytes = 0;

  struct ParentGCDetail {
    InputSectionBase *parent = nullptr;
    uint32_t liveChildren = 0;
    uint32_t deadChildren = 0;
    uint64_t liveBytes = 0;
    uint64_t deadBytes = 0;
  };
  SmallVector<ParentGCDetail, 0> details;

  for (auto &it : riscvFunctionSplitChildren) {
    ParentGCDetail detail;
    detail.parent = const_cast<InputSectionBase *>(it.first);
    for (InputSectionBase *child : it.second) {
      auto storageIt = riscvFunctionSplitRelocStorage.find(child);
      uint64_t size =
          storageIt == riscvFunctionSplitRelocStorage.end()
              ? child->getSize()
              : storageIt->second.originalEnd - storageIt->second.originalBegin;
      ++independentChildCount;
      if (child->isLive()) {
        ++liveChildCount;
        ++detail.liveChildren;
        liveChildBytes += size;
        detail.liveBytes += size;
      } else {
        ++deadChildCount;
        ++detail.deadChildren;
        deadChildBytes += size;
        detail.deadBytes += size;
      }
    }
    details.push_back(detail);
  }

  llvm::sort(details, [](const ParentGCDetail &a, const ParentGCDetail &b) {
    std::string aFile = toString(a.parent->file);
    std::string bFile = toString(b.parent->file);
    if (aFile != bFile)
      return aFile < bFile;
    return a.parent->name < b.parent->name;
  });

  message(Twine("riscv-function-sections-split: phase2a: independent GC child count: ") +
          Twine(independentChildCount));
  message(Twine("riscv-function-sections-split: phase2a: live child count: ") +
          Twine(liveChildCount));
  message(Twine("riscv-function-sections-split: phase2a: dead child count: ") +
          Twine(deadChildCount));
  message(Twine("riscv-function-sections-split: phase2a: live child bytes: ") +
          Twine(liveChildBytes));
  message(Twine("riscv-function-sections-split: phase2a: dead child bytes: ") +
          Twine(deadChildBytes));
  for (const ParentGCDetail &d : details)
    message(Twine("riscv-function-sections-split: phase2a: parent: ") +
            toString(d.parent->file) + ":(" + d.parent->name +
            ") live children " + Twine(d.liveChildren) + " dead children " +
            Twine(d.deadChildren) + " live bytes " + Twine(d.liveBytes) +
            " dead bytes " + Twine(d.deadBytes));
}

enum class RISCVLibcRefKind {
  DirectCall,
  AddressReference,
  Unknown,
};

static StringRef riscvLibcRefKindToString(RISCVLibcRefKind kind) {
  switch (kind) {
  case RISCVLibcRefKind::DirectCall:
    return "direct-call";
  case RISCVLibcRefKind::AddressReference:
    return "address-reference";
  case RISCVLibcRefKind::Unknown:
    return "unknown-reference";
  }
  llvm_unreachable("unknown RISC-V libc reference kind");
}

static RISCVLibcRefKind classifyRISCVLibcRef(RelType type) {
  switch (type) {
  case R_RISCV_CALL:
  case R_RISCV_CALL_PLT:
  case R_RISCV_JAL:
  case R_RISCV_RVC_JUMP:
    return RISCVLibcRefKind::DirectCall;
  case R_RISCV_32:
  case R_RISCV_64:
  case R_RISCV_ADD8:
  case R_RISCV_ADD16:
  case R_RISCV_ADD32:
  case R_RISCV_ADD64:
  case R_RISCV_SUB8:
  case R_RISCV_SUB16:
  case R_RISCV_SUB32:
  case R_RISCV_SUB64:
  case R_RISCV_SET6:
  case R_RISCV_SET8:
  case R_RISCV_SET16:
  case R_RISCV_SET32:
  case R_RISCV_SUB6:
  case R_RISCV_GOT_HI20:
  case R_RISCV_TLS_GOT_HI20:
  case R_RISCV_TLS_GD_HI20:
  case R_RISCV_PCREL_HI20:
  case R_RISCV_PCREL_LO12_I:
  case R_RISCV_PCREL_LO12_S:
  case R_RISCV_PLT32:
  case R_RISCV_HI20:
  case R_RISCV_LO12_I:
  case R_RISCV_LO12_S:
  case R_RISCV_RELATIVE:
    return RISCVLibcRefKind::AddressReference;
  default:
    return RISCVLibcRefKind::Unknown;
  }
}

static bool isPrintfFamilyName(StringRef name) {
  return StringSwitch<bool>(name)
      .Cases("printf", "fprintf", "sprintf", "snprintf", true)
      .Cases("vprintf", "vfprintf", "vsprintf", "vsnprintf", true)
      .Default(false);
}

static bool isPrintfFloatDependencyName(StringRef name) {
  return StringSwitch<bool>(name)
      .Cases("__extenddftf2", "__fixtfsi", "__fixunstfsi", true)
      .Cases("__floatsitf", "__floatunsitf", "__addtf3", true)
      .Cases("__divtf3", "__multf3", "__eqtf2", "__netf2", true)
      .Cases("__cmptf2", "__lttf2", "__letf2", true)
      .Cases("frexpl", "__fpclassifyl", true)
      .Default(false);
}

static bool isRISCVPrintfCoreFloatHelperName(StringRef name) {
  return StringSwitch<bool>(name)
      .Cases("__fpclassifyl", "frexpl", true)
      .Cases("__floatsitf", "__floatunsitf", "__extenddftf2", true)
      .Cases("__multf3", "__divtf3", "__addtf3", "__subtf3", true)
      .Cases("__fixtfsi", "__fixunstfsi", "__eqtf2", "__netf2", true)
      .Default(false);
}

struct RISCVLibcIncomingRef {
  Defined *sourceFunction = nullptr;
  InputSectionBase *sourceSection = nullptr;
  bool sourceLive = false;
  RelType type = R_RISCV_NONE;
  RISCVLibcRefKind kind = RISCVLibcRefKind::Unknown;
};

struct RISCVLibcFunctionNode {
  Defined *sym = nullptr;
  InputSectionBase *section = nullptr;
  SmallVector<unsigned, 0> callees;
  SmallVector<RISCVLibcIncomingRef, 0> incoming;
  uint64_t size = 0;
};

struct RISCVLibcCandidateFormat {
  std::string text;
  bool hasFloat = false;
  bool hasLongDouble = false;
};

enum class RISCVLibcFormatClass {
  ProvenConstant,
  CandidateConstant,
  DynamicOrUnknown,
  InternalForwarder,
};

static StringRef riscvLibcFormatClassToString(RISCVLibcFormatClass c) {
  switch (c) {
  case RISCVLibcFormatClass::ProvenConstant:
    return "PROVEN_CONSTANT_FORMAT";
  case RISCVLibcFormatClass::CandidateConstant:
    return "CANDIDATE_CONSTANT_FORMAT";
  case RISCVLibcFormatClass::DynamicOrUnknown:
    return "DYNAMIC_OR_UNKNOWN_FORMAT";
  case RISCVLibcFormatClass::InternalForwarder:
    return "INTERNAL_FORMAT_FORWARDER";
  }
  llvm_unreachable("unknown RISC-V libc format class");
}

struct RISCVLibcPrintfCall {
  Defined *caller = nullptr;
  InputSectionBase *sourceSection = nullptr;
  Defined *target = nullptr;
  RelType type = R_RISCV_NONE;
  uint64_t callOffset = 0;
  RISCVLibcFormatClass formatClass = RISCVLibcFormatClass::DynamicOrUnknown;
  RISCVLibcCandidateFormat provenFormat;
  std::string proof;
  std::string reason;
  std::string entryCalleeSavedReason;
  std::string entryCalleeSavedDetail;
  std::string localDominatingReason;
  std::string localDominatingDetail;
  std::string loopCarriedReason;
  std::string loopCarriedDetail;
  SmallVector<RISCVLibcCandidateFormat, 0> candidateFormats;
};

enum class RISCVLibcStackMemKind {
  None,
  CLWSP,
  CSWSP,
  LW,
  SW,
};

struct RISCVLibcEntryCalleeSavedDiag {
  std::string reason;
  int copySrc = -1;
  uint64_t copyOffset = std::numeric_limits<uint64_t>::max();
  uint64_t prefixEndOffset = std::numeric_limits<uint64_t>::max();
  uint64_t firstControlFlowOffset = std::numeric_limits<uint64_t>::max();
  std::string firstControlFlowKind = "none";
  std::string firstControlFlowRelocs = "none";
  uint32_t firstControlFlowRaw = 0;
  int firstControlFlowQuadrant = -1;
  int firstControlFlowFunct3 = -1;
  uint64_t candidateHi = std::numeric_limits<uint64_t>::max();
  uint64_t candidateLo = std::numeric_limits<uint64_t>::max();
  int candidateDst = -1;
  std::string candidateSymbol = "none";
  std::string candidateRejectReason = "none";
};

struct RISCVLibcLocalDominatingDiag {
  std::string reason;
  uint64_t copyOffset = std::numeric_limits<uint64_t>::max();
  int copySrc = -1;
  uint64_t nearestDefOffset = std::numeric_limits<uint64_t>::max();
  uint64_t hiOffset = std::numeric_limits<uint64_t>::max();
  uint64_t loOffset = std::numeric_limits<uint64_t>::max();
  uint64_t initStart = std::numeric_limits<uint64_t>::max();
  uint64_t initComplete = std::numeric_limits<uint64_t>::max();
  uint64_t externalEntrySource = std::numeric_limits<uint64_t>::max();
  uint64_t externalEntryTarget = std::numeric_limits<uint64_t>::max();
  uint64_t unknownControlFlowOffset = std::numeric_limits<uint64_t>::max();
};

struct RISCVLibcLoopCarriedDiag {
  std::string reason;
  uint64_t regionStart = std::numeric_limits<uint64_t>::max();
  uint64_t regionEnd = std::numeric_limits<uint64_t>::max();
  uint64_t backedgeSource = std::numeric_limits<uint64_t>::max();
  uint64_t backedgeTarget = std::numeric_limits<uint64_t>::max();
  uint64_t externalEntrySource = std::numeric_limits<uint64_t>::max();
  uint64_t externalEntryTarget = std::numeric_limits<uint64_t>::max();
  uint64_t unknownControlFlowOffset = std::numeric_limits<uint64_t>::max();
};

struct RISCVLibcPrintfCoreFloatCall {
  InputSectionBase *sourceSection = nullptr;
  Defined *sourceFunction = nullptr;
  Defined *helper = nullptr;
  InputSectionBase *targetSection = nullptr;
  uint64_t helperSize = 0;
  uint64_t relocOffset = 0;
  uint64_t callInsnOffset = 0;
  RelType relocType = R_RISCV_NONE;
};

struct RISCVLibcPrintfCoreFloatRegion {
  InputSectionBase *section = nullptr;
  Defined *function = nullptr;
  uint64_t start = std::numeric_limits<uint64_t>::max();
  uint64_t end = 0;
  uint32_t helperCallCount = 0;
};

enum class RISCVLibcGlobalRouteKind {
  DirectCall,
  InternalForwarder,
  NonCallReference,
  DirectPrintfCoreRoute,
  Unresolved,
};

enum class RISCVLibcAuditReachabilityMode {
  PostGCLiveOnly,
  PreGCConservative,
};

static StringRef
riscvLibcGlobalRouteKindToString(RISCVLibcGlobalRouteKind kind) {
  switch (kind) {
  case RISCVLibcGlobalRouteKind::DirectCall:
    return "direct-call";
  case RISCVLibcGlobalRouteKind::InternalForwarder:
    return "recognized-internal-forwarder";
  case RISCVLibcGlobalRouteKind::NonCallReference:
    return "address-taken";
  case RISCVLibcGlobalRouteKind::DirectPrintfCoreRoute:
    return "direct-printf-core";
  case RISCVLibcGlobalRouteKind::Unresolved:
    return "unresolved";
  }
  llvm_unreachable("unknown RISC-V libc global route kind");
}

struct RISCVLibcAuditPerfStats {
  uint32_t decodedSourceFunctions = 0;
  uint64_t decodedInstructionCount = 0;
  uint32_t decodeCacheHits = 0;
  uint32_t decodeCacheMisses = 0;
  uint32_t relocCacheHits = 0;
  uint32_t relocCacheMisses = 0;
};

struct RISCVLibcPrintfCallCollectionStats {
  uint32_t rawPrintfDirectCallRecords = 0;
  uint32_t duplicatePrintfDirectCallRecords = 0;
};

struct RISCVLibcGlobalRouteAuditStats {
  uint32_t entryCalls = 0;
  uint32_t provenNonFloatEntryCalls = 0;
  uint32_t floatEntryCalls = 0;
  uint32_t unknownEntryCalls = 0;
  uint32_t internalForwarders = 0;
  uint32_t nonCallRefs = 0;
  uint32_t addressTakenRefs = 0;
  uint32_t directPrintfCoreRoutes = 0;
  uint32_t unrecognizedPrintfCoreRoutes = 0;
  uint32_t unresolvedRoutes = 0;
  uint32_t directEntryRoutes = 0;
  uint32_t matchedProofRoutes = 0;
  uint32_t missingProofRoutes = 0;
  uint32_t aliasRoutes = 0;
  bool gateReady = false;
};

struct RISCVPrintfSpecializationStats {
  bool applied = false;
  uint32_t floatCallsNopped = 0;
  uint32_t callRelocsRemoved = 0;
  uint32_t relaxRelocsRemoved = 0;
  std::string fallbackReason = "none";
};

template <class RelTy> static int64_t getRISCVLibcAddend(const RelTy &rel) {
  if constexpr (RelTy::IsRela)
    return rel.r_addend;
  return 0;
}

static bool isRISCVLibcReadOnlyData(InputSectionBase &sec) {
  return (sec.flags & SHF_ALLOC) && !(sec.flags & SHF_WRITE) &&
         !(sec.flags & SHF_EXECINSTR) && sec.type == SHT_PROGBITS;
}

static std::string symbolFileName(const Defined &d) {
  return d.file ? lld::toString(d.file) : std::string("<internal>");
}

static bool readCStringAt(InputSectionBase &sec, uint64_t off,
                          std::string &out) {
  ArrayRef<uint8_t> data = sec.content();
  if (off >= data.size())
    return false;

  constexpr size_t maxLen = 512;
  out.clear();
  for (uint64_t i = off; i < data.size() && out.size() < maxLen; ++i) {
    uint8_t c = data[i];
    if (c == 0)
      return !out.empty();
    if ((c < 0x20 || c > 0x7e) && c != '\n' && c != '\t' && c != '\r')
      return false;
    out.push_back(static_cast<char>(c));
  }
  return false;
}

static void scanPrintfFormat(StringRef s, bool &hasFloat,
                             bool &hasLongDouble) {
  hasFloat = false;
  hasLongDouble = false;
  for (size_t i = 0; i < s.size(); ++i) {
    if (s[i] != '%')
      continue;
    ++i;
    if (i < s.size() && s[i] == '%')
      continue;
    while (i < s.size() && StringRef("-+ #0").contains(s[i]))
      ++i;
    if (i < s.size() && s[i] == '*')
      ++i;
    else
      while (i < s.size() && isDigit(s[i]))
        ++i;
    if (i < s.size() && s[i] == '.') {
      ++i;
      if (i < s.size() && s[i] == '*')
        ++i;
      else
        while (i < s.size() && isDigit(s[i]))
          ++i;
    }

    bool longDouble = false;
    if (i < s.size() && s[i] == 'L') {
      longDouble = true;
      ++i;
    } else if (i + 1 < s.size() && s.substr(i, 2) == "hh") {
      i += 2;
    } else if (i + 1 < s.size() && s.substr(i, 2) == "ll") {
      i += 2;
    } else if (i < s.size() && StringRef("hljzt").contains(s[i])) {
      ++i;
    }

    if (i >= s.size())
      break;
    if (StringRef("fFeEgGaA").contains(s[i])) {
      hasFloat = true;
      hasLongDouble |= longDouble;
    }
  }
}

static int getRISCVPrintfFormatArgReg(StringRef name) {
  return StringSwitch<int>(name)
      .Cases("printf", "vprintf", 10)       // a0
      .Cases("fprintf", "vfprintf", 11)     // a1
      .Cases("sprintf", "vsprintf", 11)     // a1
      .Cases("snprintf", "vsnprintf", 12)   // a2
      .Default(-1);
}

static bool isRISCVPrintfInternalForwarder(StringRef caller, StringRef target) {
  return caller == "printf" && target == "vfprintf";
}

struct RISCVLibcRelocTarget {
  Defined *sym = nullptr;
  uint64_t offset = 0;
  int64_t addend = 0;
  bool pcrelHi = false;
  bool absHi = false;
  bool absLoI = false;
  bool lo = false;
};

struct RISCVLibcControlFlowRelocInfo {
  RelType type = R_RISCV_NONE;
  Symbol *sym = nullptr;
  int64_t addend = 0;
  InputSectionBase *targetSection = nullptr;
  uint64_t targetOffset = 0;
  bool hasTarget = false;
};

struct RISCVLibcInsn {
  uint64_t offset = 0;
  uint32_t raw = 0;
  uint8_t size = 0;
  int rd = -1;
  int rs1 = -1;
  int rs2 = -1;
  int copySrc = -1;
  RISCVLibcStackMemKind stackMemKind = RISCVLibcStackMemKind::None;
  int64_t stackOffset = 0;
  int stackStoreSrc = -1;
  bool controlFlow = false;
  bool call = false;
  bool addi = false;
  bool copy = false;
  bool lui = false;
  bool auipc = false;
  bool writesRd = false;
  bool supported = true;
};

struct RISCVLibcCalleeSavedConstCandidate {
  const RISCVLibcInsn *copyInsn = nullptr;
  const RISCVLibcInsn *hiInsn = nullptr;
  const RISCVLibcInsn *loInsn = nullptr;
  int savedReg = -1;
};

struct RISCVLibcFunctionDecode {
  InputSectionBase *section = nullptr;
  Defined *function = nullptr;
  uint64_t funcStart = 0;
  uint64_t funcEnd = 0;
  uint64_t decodedEnd = 0;
  SmallVector<RISCVLibcInsn, 0> instructions;
  bool decodeOk = true;
};

static bool readRISCVLibcInsn(ArrayRef<uint8_t> data, uint64_t off,
                              RISCVLibcInsn &insn) {
  if (off + 2 > data.size())
    return false;
  uint16_t half = llvm::support::endian::read16le(data.data() + off);
  insn = {};
  insn.offset = off;
  insn.raw = half;
  if ((half & 3) != 3) {
    insn.size = 2;
    insn.supported = false;
    uint16_t quadrant = half & 3;
    uint16_t funct3 = (half >> 13) & 7;
    switch (quadrant) {
    case 0:
      switch (funct3) {
      case 0: // C.ADDI4SPN.
        insn.rd = 8 + ((half >> 2) & 7);
        insn.writesRd = true;
        insn.supported = true;
        break;
      case 2: // C.LW.
        insn.rd = 8 + ((half >> 2) & 7);
        insn.writesRd = true;
        insn.supported = true;
        break;
      case 6: // C.SW.
        insn.rs1 = 8 + ((half >> 7) & 7);
        insn.rs2 = 8 + ((half >> 2) & 7);
        insn.supported = true;
        break;
      default:
        break;
      }
      break;
    case 1:
      switch (funct3) {
      case 0: // C.ADDI.
        insn.rd = (half >> 7) & 0x1f;
        insn.rs1 = insn.rd;
        insn.addi = true;
        insn.writesRd = insn.rd != 0;
        insn.supported = true;
        break;
      case 1: // C.JAL on RV32.
      case 5: // C.J.
        insn.controlFlow = true;
        insn.call = funct3 == 1;
        insn.supported = true;
        break;
      case 2: // C.LI.
        insn.rd = (half >> 7) & 0x1f;
        insn.writesRd = insn.rd != 0;
        insn.supported = true;
        break;
      case 3: // C.LUI / C.ADDI16SP.
        insn.rd = (half >> 7) & 0x1f;
        insn.lui = insn.rd != 0 && insn.rd != 2;
        insn.writesRd = insn.rd != 0;
        insn.supported = true;
        break;
      case 4:
        if (((half >> 10) & 3) == 0) { // C.SRLI.
          insn.rd = 8 + ((half >> 7) & 7);
          insn.rs1 = insn.rd;
          insn.writesRd = true;
          insn.supported = true;
        } else if (((half >> 10) & 3) == 1) { // C.SRAI.
          insn.rd = 8 + ((half >> 7) & 7);
          insn.rs1 = insn.rd;
          insn.writesRd = true;
          insn.supported = true;
        } else if (((half >> 10) & 3) == 2) { // C.ANDI.
          insn.rd = 8 + ((half >> 7) & 7);
          insn.rs1 = insn.rd;
          insn.writesRd = true;
          insn.supported = true;
        } else {
          insn.rd = 8 + ((half >> 7) & 7);
          insn.rs1 = insn.rd;
          insn.rs2 = 8 + ((half >> 2) & 7);
          insn.writesRd = true;
          insn.supported = true;
        }
        break;
      case 6: // C.BEQZ.
      case 7: // C.BNEZ.
        insn.controlFlow = true;
        insn.supported = true;
        break;
      default:
        break;
      }
      break;
    case 2:
      switch (funct3) {
      case 0: // C.SLLI.
        insn.rd = (half >> 7) & 0x1f;
        insn.rs1 = insn.rd;
        insn.writesRd = insn.rd != 0;
        insn.supported = true;
        break;
      case 2: // C.LWSP.
        insn.rd = (half >> 7) & 0x1f;
        insn.writesRd = insn.rd != 0;
        insn.rs1 = 2;
        insn.stackMemKind = RISCVLibcStackMemKind::CLWSP;
        insn.stackOffset = (((half >> 4) & 0x7) << 2) |
                           (((half >> 12) & 0x1) << 5) |
                           (((half >> 2) & 0x3) << 6);
        insn.supported = true;
        break;
      case 6: // C.SWSP.
        insn.rs2 = (half >> 2) & 0x1f;
        insn.rs1 = 2;
        insn.stackMemKind = RISCVLibcStackMemKind::CSWSP;
        insn.stackStoreSrc = insn.rs2;
        insn.stackOffset = (((half >> 9) & 0xf) << 2) |
                           (((half >> 7) & 0x3) << 6);
        insn.supported = true;
        break;
      case 4: {
        insn.rd = (half >> 7) & 0x1f;
        insn.rs2 = (half >> 2) & 0x1f;
        bool bit12 = half & 0x1000;
        if (bit12 && insn.rs2 == 0) { // C.JALR.
          insn.controlFlow = true;
          insn.call = true;
          insn.supported = true;
        } else if (!bit12 && insn.rs2 == 0) { // C.JR.
          insn.controlFlow = true;
          insn.supported = true;
        } else {
          // C.MV or C.ADD. Both write rd.
          insn.rs1 = bit12 ? insn.rd : 0;
          insn.writesRd = insn.rd != 0;
          insn.copy = !bit12 && insn.rd != 0 && insn.rs2 != 0;
          insn.copySrc = insn.copy ? insn.rs2 : -1;
          insn.supported = true;
        }
        break;
      }
      default:
        break;
      }
      break;
    default:
      break;
    }
    return true;
  }

  if (off + 4 > data.size())
    return false;
  uint32_t raw = llvm::support::endian::read32le(data.data() + off);
  insn.raw = raw;
  insn.size = 4;
  uint32_t opcode = raw & 0x7f;
  insn.rd = (raw >> 7) & 0x1f;
  insn.rs1 = (raw >> 15) & 0x1f;
  insn.rs2 = (raw >> 20) & 0x1f;
  switch (opcode) {
  case 0x37: // LUI.
    insn.lui = true;
    insn.writesRd = insn.rd != 0;
    break;
  case 0x17: // AUIPC.
    insn.auipc = true;
    insn.writesRd = insn.rd != 0;
    break;
  case 0x13: // OP-IMM.
    insn.addi = ((raw >> 12) & 7) == 0;
    insn.writesRd = insn.rd != 0;
    if (insn.addi && insn.rd != 0 && insn.rs1 != 0 &&
        SignExtend64<12>(raw >> 20) == 0) {
      insn.copy = true;
      insn.copySrc = insn.rs1;
    }
    break;
  case 0x67: // JALR.
    insn.controlFlow = true;
    insn.call = insn.rd != 0;
    insn.writesRd = insn.rd != 0;
    break;
  case 0x6f: // JAL.
    insn.controlFlow = true;
    insn.call = insn.rd != 0;
    insn.writesRd = insn.rd != 0;
    break;
  case 0x63: // Conditional branch.
    insn.controlFlow = true;
    break;
  case 0x33: // OP.
  case 0x1b: // OP-IMM-32.
  case 0x2f: // AMO.
  case 0x3b: // OP-32.
  case 0x0f: // MISC-MEM.
  case 0x73: // SYSTEM.
    insn.writesRd = insn.rd != 0;
    break;
  case 0x03: // LOAD.
    insn.writesRd = insn.rd != 0;
    if (((raw >> 12) & 7) == 2 && insn.rs1 == 2) {
      insn.stackMemKind = RISCVLibcStackMemKind::LW;
      insn.stackOffset = SignExtend64<12>(raw >> 20);
    }
    break;
  case 0x23: // STORE.
    if (((raw >> 12) & 7) == 2 && insn.rs1 == 2) {
      insn.stackMemKind = RISCVLibcStackMemKind::SW;
      insn.stackStoreSrc = insn.rs2;
      uint32_t imm = ((raw >> 7) & 0x1f) | (((raw >> 25) & 0x7f) << 5);
      insn.stackOffset = SignExtend64<12>(imm);
    }
    break;
  default:
    insn.supported = false;
    break;
  }
  return true;
}

static bool riscvLibcInsnWritesReg(const RISCVLibcInsn &insn, int reg) {
  return insn.writesRd && insn.rd == reg;
}

static RISCVLibcFunctionDecode &
getRISCVLibcFunctionDecodeCached(
    InputSectionBase &sec, Defined &func,
    std::map<std::pair<InputSectionBase *, Defined *>, RISCVLibcFunctionDecode>
        &cache,
    RISCVLibcAuditPerfStats &stats) {
  std::pair<InputSectionBase *, Defined *> key{&sec, &func};
  auto it = cache.find(key);
  if (it != cache.end()) {
    ++stats.decodeCacheHits;
    return it->second;
  }

  ++stats.decodeCacheMisses;
  RISCVLibcFunctionDecode decoded;
  decoded.section = &sec;
  decoded.function = &func;
  decoded.funcStart = func.value;
  decoded.funcEnd = sec.content().size();
  decoded.decodedEnd = decoded.funcStart;
  if (func.size != 0 && func.value + func.size < decoded.funcEnd)
    decoded.funcEnd = func.value + func.size;
  ArrayRef<uint8_t> data = sec.content();
  for (uint64_t off = decoded.funcStart; off < decoded.funcEnd;) {
    RISCVLibcInsn insn;
    if (!readRISCVLibcInsn(data, off, insn) || off + insn.size > decoded.funcEnd) {
      decoded.decodeOk = false;
      break;
    }
    decoded.instructions.push_back(insn);
    off += insn.size;
    decoded.decodedEnd = off;
  }
  ++stats.decodedSourceFunctions;
  stats.decodedInstructionCount += decoded.instructions.size();
  auto inserted = cache.insert({key, std::move(decoded)});
  return inserted.first->second;
}

static bool collectRISCVLibcInsnsBeforeCall(
    const RISCVLibcFunctionDecode &decoded, uint64_t callOff,
    SmallVectorImpl<RISCVLibcInsn> &insns, std::string &reason,
    uint32_t maxInsns = 0) {
  bool reachedCallBoundary = decoded.funcStart == callOff;
  for (const RISCVLibcInsn &insn : decoded.instructions) {
    if (insn.offset == callOff) {
      reachedCallBoundary = true;
      break;
    }
    if (insn.offset > callOff)
      break;
    if (insn.offset + insn.size > callOff) {
      reason = "decode-did-not-reach-call-offset";
      return false;
    }
    insns.push_back(insn);
    if (maxInsns != 0 && insns.size() > maxInsns)
      insns.erase(insns.begin());
    if (insn.offset + insn.size == callOff) {
      reachedCallBoundary = true;
      break;
    }
  }
  if (!reachedCallBoundary) {
    reason = callOff > decoded.decodedEnd ? "decode-failed"
                                          : "decode-did-not-reach-call-offset";
    return false;
  }
  return true;
}

static bool targetRISCVLibcCString(Defined &d, int64_t addend,
                                   RISCVLibcCandidateFormat &format) {
  auto *targetSec = dyn_cast_or_null<InputSectionBase>(d.section);
  if (!targetSec || !isRISCVLibcReadOnlyData(*targetSec))
    return false;
  uint64_t off = 0;
  if (!checkedAddend(d.value, addend, off))
    return false;
  std::string text;
  if (!readCStringAt(*targetSec, off, text))
    return false;
  format.text = std::move(text);
  scanPrintfFormat(format.text, format.hasFloat, format.hasLongDouble);
  return true;
}

template <class ELFT, class RelTy>
static void recordRISCVLibcRelocTarget(
    InputSectionBase &sec, const RelTy &rel,
    DenseMap<uint64_t, RISCVLibcRelocTarget> &targets) {
  RelType type = rel.getType(config->isMips64EL);
  if (type != R_RISCV_HI20 && type != R_RISCV_PCREL_HI20 &&
      type != R_RISCV_LO12_I && type != R_RISCV_LO12_S &&
      type != R_RISCV_PCREL_LO12_I && type != R_RISCV_PCREL_LO12_S)
    return;
  Symbol &target = sec.getFile<ELFT>()->getRelocTargetSym(rel);
  Defined *d = dyn_cast<Defined>(&target);
  if (!d)
    return;
  RISCVLibcRelocTarget t;
  t.sym = d;
  t.offset = rel.r_offset;
  t.addend = getRISCVLibcAddend(rel);
  t.pcrelHi = type == R_RISCV_PCREL_HI20;
  t.absHi = type == R_RISCV_HI20;
  t.absLoI = type == R_RISCV_LO12_I;
  t.lo = type == R_RISCV_LO12_I || type == R_RISCV_LO12_S ||
         type == R_RISCV_PCREL_LO12_I || type == R_RISCV_PCREL_LO12_S;
  targets[rel.r_offset] = t;
}

template <class ELFT>
static DenseMap<uint64_t, RISCVLibcRelocTarget>
getRISCVLibcRelocTargets(InputSectionBase &sec) {
  DenseMap<uint64_t, RISCVLibcRelocTarget> targets;
  if (!sec.file)
    return targets;
  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  for (const auto &rel : rels.rels)
    recordRISCVLibcRelocTarget<ELFT>(sec, rel, targets);
  for (const auto &rel : rels.relas)
    recordRISCVLibcRelocTarget<ELFT>(sec, rel, targets);
  return targets;
}

template <class ELFT>
static DenseMap<uint64_t, RISCVLibcRelocTarget> &
getRISCVLibcRelocTargetsCached(
    InputSectionBase &sec,
    std::map<InputSectionBase *, DenseMap<uint64_t, RISCVLibcRelocTarget>>
        &cache,
    RISCVLibcAuditPerfStats &stats) {
  auto it = cache.find(&sec);
  if (it != cache.end()) {
    ++stats.relocCacheHits;
    return it->second;
  }
  ++stats.relocCacheMisses;
  auto inserted = cache.insert({&sec, getRISCVLibcRelocTargets<ELFT>(sec)});
  return inserted.first->second;
}

template <class ELFT, class RelTy>
static void recordRISCVLibcControlFlowReloc(
    InputSectionBase &sec, const RelTy &rel,
    DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &targets) {
  RelType type = rel.getType(config->isMips64EL);
  if (type != R_RISCV_BRANCH && type != R_RISCV_JAL &&
      type != R_RISCV_RVC_BRANCH && type != R_RISCV_RVC_JUMP &&
      type != R_RISCV_CALL && type != R_RISCV_CALL_PLT)
    return;

  RISCVLibcControlFlowRelocInfo info;
  info.type = type;
  info.addend = getRISCVLibcAddend(rel);
  Symbol &target = sec.getFile<ELFT>()->getRelocTargetSym(rel);
  info.sym = &target;
  if (Defined *d = dyn_cast<Defined>(&target)) {
    info.targetSection = dyn_cast_or_null<InputSectionBase>(d->section);
    if (info.targetSection)
      info.hasTarget = checkedAddend(d->value, info.addend, info.targetOffset);
  }
  targets[rel.r_offset].push_back(info);
}

template <class ELFT>
static DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
getRISCVLibcControlFlowRelocs(InputSectionBase &sec) {
  DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>> targets;
  if (!sec.file)
    return targets;
  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  for (const auto &rel : rels.rels)
    recordRISCVLibcControlFlowReloc<ELFT>(sec, rel, targets);
  for (const auto &rel : rels.relas)
    recordRISCVLibcControlFlowReloc<ELFT>(sec, rel, targets);
  return targets;
}

template <class ELFT>
static DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>> &
getRISCVLibcControlFlowRelocsCached(
    InputSectionBase &sec,
    std::map<InputSectionBase *,
             DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>>
        &cache) {
  auto it = cache.find(&sec);
  if (it != cache.end())
    return it->second;
  auto inserted =
      cache.insert({&sec, getRISCVLibcControlFlowRelocs<ELFT>(sec)});
  return inserted.first->second;
}

static bool hasRISCVLibcControlFlowRelocTypeAt(
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &relocs,
    uint64_t off, ArrayRef<RelType> types) {
  auto it = relocs.find(off);
  if (it == relocs.end())
    return false;
  return llvm::any_of(it->second, [&](const RISCVLibcControlFlowRelocInfo &r) {
    return llvm::is_contained(types, r.type);
  });
}

static bool isRISCVLibcRelocTargetFunc(
    const RISCVLibcControlFlowRelocInfo &reloc) {
  if (Defined *d = dyn_cast_or_null<Defined>(reloc.sym))
    return d->type == STT_FUNC;
  return false;
}

static bool isRISCVLibcNormalDirectCall(
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &relocs,
    const RISCVLibcInsn &insn) {
  if (!insn.controlFlow || !insn.call)
    return false;
  if (insn.size == 4 && (insn.raw & 0x7f) == 0x67 && insn.offset >= 4)
    return hasRISCVLibcControlFlowRelocTypeAt(
        relocs, insn.offset - 4, {R_RISCV_CALL, R_RISCV_CALL_PLT});
  auto it = relocs.find(insn.offset);
  if (it == relocs.end())
    return false;
  bool isRV32CJal =
      insn.size == 2 && (((static_cast<uint16_t>(insn.raw) >> 13) & 0x7) == 1);
  for (const RISCVLibcControlFlowRelocInfo &r : it->second) {
    if (r.type == R_RISCV_CALL || r.type == R_RISCV_CALL_PLT)
      return true;
    if (r.type == R_RISCV_JAL && isRISCVLibcRelocTargetFunc(r))
      return true;
    if (r.type == R_RISCV_RVC_JUMP && isRV32CJal &&
        isRISCVLibcRelocTargetFunc(r))
      return true;
  }
  return false;
}

static bool isRISCVLibcReturn(const RISCVLibcInsn &insn) {
  if (!insn.controlFlow || insn.call)
    return false;
  if (insn.size == 4 && (insn.raw & 0x7f) == 0x67)
    return insn.rd == 0 && insn.rs1 == 1 &&
           SignExtend64<12>(insn.raw >> 20) == 0;
  if (insn.size != 2)
    return false;
  uint16_t half = static_cast<uint16_t>(insn.raw);
  uint16_t quadrant = half & 0x3;
  uint16_t funct3 = (half >> 13) & 0x7;
  bool bit12 = half & 0x1000;
  int rd = (half >> 7) & 0x1f;
  int rs2 = (half >> 2) & 0x1f;
  return quadrant == 2 && funct3 == 4 && !bit12 && rd == 1 && rs2 == 0;
}

static const RISCVLibcControlFlowRelocInfo *
getRISCVLibcDirectBranchTarget(
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &relocs,
    const RISCVLibcInsn &insn) {
  if (!insn.controlFlow || insn.call)
    return nullptr;
  auto it = relocs.find(insn.offset);
  if (it == relocs.end())
    return nullptr;
  const RISCVLibcControlFlowRelocInfo *found = nullptr;
  for (const RISCVLibcControlFlowRelocInfo &r : it->second) {
    if (r.type != R_RISCV_BRANCH && r.type != R_RISCV_JAL &&
        r.type != R_RISCV_RVC_BRANCH && r.type != R_RISCV_RVC_JUMP)
      continue;
    if (found)
      return nullptr;
    found = &r;
  }
  return found;
}

static bool hasRISCVLibcExternalEntryToProtectedInterval(
    InputSectionBase &sec,
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &relocs,
    uint64_t initStart, uint64_t copyOffset,
    RISCVLibcLocalDominatingDiag *diag = nullptr) {
  for (const auto &entry : relocs) {
    uint64_t sourceOffset = entry.first;
    for (const RISCVLibcControlFlowRelocInfo &r : entry.second) {
      if (r.type != R_RISCV_BRANCH && r.type != R_RISCV_JAL &&
          r.type != R_RISCV_RVC_BRANCH && r.type != R_RISCV_RVC_JUMP &&
          r.type != R_RISCV_CALL && r.type != R_RISCV_CALL_PLT)
        continue;
      if (!r.hasTarget || r.targetSection != &sec)
        continue;
      if (r.targetOffset > initStart && r.targetOffset <= copyOffset &&
          (sourceOffset <= initStart || sourceOffset > copyOffset)) {
        if (diag) {
          diag->externalEntrySource = sourceOffset;
          diag->externalEntryTarget = r.targetOffset;
        }
        return true;
      }
    }
  }
  return false;
}

static bool isRISCVLibcDirectBranchOrJumpReloc(RelType type) {
  return type == R_RISCV_BRANCH || type == R_RISCV_JAL ||
         type == R_RISCV_RVC_BRANCH || type == R_RISCV_RVC_JUMP;
}

static bool isRISCVLibcControlFlowAuditReloc(RelType type) {
  return isRISCVLibcDirectBranchOrJumpReloc(type);
}

static bool containsRISCVLibcOffset(const RISCVLibcPrintfCoreFloatRegion &r,
                                    uint64_t off) {
  return off >= r.start && off <= r.end;
}

static uint64_t getRISCVLibcCallInsnOffset(const RISCVLibcFunctionDecode &d,
                                           uint64_t relocOffset) {
  for (const RISCVLibcInsn &insn : d.instructions) {
    if (insn.offset == relocOffset)
      return insn.offset;
    if (insn.size == 4 && (insn.raw & 0x7f) == 0x67 &&
        insn.offset >= 4 && insn.offset - 4 == relocOffset)
      return insn.offset;
  }
  return relocOffset;
}

static const RISCVLibcInsn *
getRISCVLibcInsnAt(const RISCVLibcFunctionDecode &d, uint64_t off) {
  for (const RISCVLibcInsn &insn : d.instructions)
    if (insn.offset == off)
      return &insn;
  return nullptr;
}

static const RISCVLibcInsn *
getRISCVLibcNextInsn(const RISCVLibcFunctionDecode &d,
                     const RISCVLibcInsn &insn) {
  uint64_t next = insn.offset + insn.size;
  return getRISCVLibcInsnAt(d, next);
}

static bool isRISCVLibcLinkReg(int reg) { return reg == 1 || reg == 5; }

static std::optional<bool> isRISCVLibcCallLikeControlFlow(
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &relocs,
    const RISCVLibcInsn &insn) {
  if (!insn.controlFlow)
    return false;
  if (isRISCVLibcNormalDirectCall(relocs, insn))
    return true;
  if (insn.size == 4) {
    uint32_t opcode = insn.raw & 0x7f;
    if (opcode == 0x6f || opcode == 0x67)
      return isRISCVLibcLinkReg(insn.rd);
    if (opcode == 0x63)
      return false;
    return std::nullopt;
  }
  uint16_t half = static_cast<uint16_t>(insn.raw);
  uint16_t quadrant = half & 0x3;
  uint16_t funct3 = (half >> 13) & 0x7;
  bool bit12 = half & 0x1000;
  int rd = (half >> 7) & 0x1f;
  int rs2 = (half >> 2) & 0x1f;
  if (quadrant == 1 && funct3 == 1)
    return true; // C.JAL on RV32.
  if (quadrant == 1 && (funct3 == 5 || funct3 == 6 || funct3 == 7))
    return false;
  if (quadrant == 2 && funct3 == 4 && rs2 == 0) {
    if (bit12)
      return true; // C.JALR links through ra.
    return false;  // C.JR.
  }
  if (insn.call)
    return isRISCVLibcLinkReg(rd);
  return std::nullopt;
}

static bool isRISCVLibcNonCallControlFlow(
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &relocs,
    const RISCVLibcInsn &insn) {
  if (!insn.controlFlow)
    return false;
  std::optional<bool> callLike = isRISCVLibcCallLikeControlFlow(relocs, insn);
  return !callLike || !*callLike;
}

static std::optional<bool> hasRISCVLibcKnownFallthrough(
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &relocs,
    const RISCVLibcInsn &insn) {
  if (!insn.controlFlow)
    return true;
  std::optional<bool> callLike = isRISCVLibcCallLikeControlFlow(relocs, insn);
  if (!callLike)
    return std::nullopt;
  if (*callLike)
    return true;
  if (isRISCVLibcReturn(insn))
    return false;
  if (insn.size == 4) {
    uint32_t opcode = insn.raw & 0x7f;
    if (opcode == 0x63)
      return true;
    if (opcode == 0x6f || opcode == 0x67)
      return false;
    return std::nullopt;
  }
  uint16_t half = static_cast<uint16_t>(insn.raw);
  uint16_t quadrant = half & 0x3;
  uint16_t funct3 = (half >> 13) & 0x7;
  if (quadrant == 1 && (funct3 == 6 || funct3 == 7))
    return true;
  if (quadrant == 1 && funct3 == 5)
    return false;
  if (quadrant == 2 && funct3 == 4)
    return false;
  return std::nullopt;
}

static std::string hexOffset(uint64_t off) {
  return (Twine("0x") + llvm::utohexstr(off)).str();
}

static std::string hexOffsetOrNone(uint64_t off) {
  return off == std::numeric_limits<uint64_t>::max() ? std::string("none")
                                                     : hexOffset(off);
}

static StringRef riscvLibcRegName(int reg) {
  switch (reg) {
  case 10:
    return "a0";
  case 11:
    return "a1";
  case 12:
    return "a2";
  default:
    break;
  }
  return "unknown";
}

static std::string riscvLibcXRegName(int reg) {
  if (reg < 0)
    return "none";
  return (Twine("x") + Twine(reg)).str();
}

static StringRef riscvLibcSRegName(int reg) {
  switch (reg) {
  case 8:
    return "S0";
  case 9:
    return "S1";
  case 18:
    return "S2";
  case 19:
    return "S3";
  case 20:
    return "S4";
  case 21:
    return "S5";
  case 22:
    return "S6";
  case 23:
    return "S7";
  case 24:
    return "S8";
  case 25:
    return "S9";
  case 26:
    return "S10";
  case 27:
    return "S11";
  default:
    break;
  }
  return "UNKNOWN";
}

static bool isRISCVIntegerCalleeSavedReg(int reg) {
  return reg == 8 || reg == 9 || (reg >= 18 && reg <= 27);
}

static StringRef riscvLibcInsnKind(const RISCVLibcInsn &insn) {
  if (!insn.supported)
    return "UNKNOWN";
  if (insn.stackMemKind == RISCVLibcStackMemKind::CLWSP)
    return "C_LWSP";
  if (insn.stackMemKind == RISCVLibcStackMemKind::CSWSP)
    return "C_SWSP";
  if (insn.stackMemKind == RISCVLibcStackMemKind::LW)
    return "LW";
  if (insn.stackMemKind == RISCVLibcStackMemKind::SW)
    return "SW";
  if (insn.lui)
    return "LUI";
  if (insn.auipc)
    return "AUIPC";
  if (insn.copy)
    return insn.size == 2 ? "C_MV" : "ADDI_COPY";
  if (insn.addi)
    return insn.size == 2 ? "C_ADDI" : "ADDI";
  if (insn.controlFlow && insn.call)
    return insn.size == 2 ? "C_JALR_OR_C_JAL" : "JAL_OR_JALR";
  if (insn.controlFlow)
    return insn.size == 2 ? "RVC_BRANCH_OR_JUMP" : "BRANCH_OR_JUMP";
  return "OTHER";
}

static StringRef riscvLibcStackMemKindToString(RISCVLibcStackMemKind kind) {
  switch (kind) {
  case RISCVLibcStackMemKind::None:
    return "none";
  case RISCVLibcStackMemKind::CLWSP:
    return "C_LWSP";
  case RISCVLibcStackMemKind::CSWSP:
    return "C_SWSP";
  case RISCVLibcStackMemKind::LW:
    return "LW";
  case RISCVLibcStackMemKind::SW:
    return "SW";
  }
  llvm_unreachable("unknown RISC-V libc stack memory kind");
}

struct RISCVLibcRegDefDiag {
  std::string kind = "unknown";
  uint64_t offset = std::numeric_limits<uint64_t>::max();
  int copySrc = -1;
  bool copySrcIsCalleeSaved = false;
  bool constantFormatProven = false;
  std::string format = "none";
  std::string reason = "not-proven";
};

struct RISCVLibcStackSlotCFGAudit {
  bool sameSlotClobber = false;
  bool externalEntry = false;
  bool spModified = false;
  bool backedgeBypass = false;
  bool unknownControlFlow = false;
  bool safe = false;
  std::string reason = "none";
};

static RISCVLibcStackSlotCFGAudit auditRISCVLibcStackSlotCFG(
    InputSectionBase &sec, const RISCVLibcFunctionDecode &decoded,
    ArrayRef<RISCVLibcInsn> allInsns, size_t storeIndex, size_t loadIndex,
    const DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &controlFlowRelocs,
    int64_t stackOffset) {
  RISCVLibcStackSlotCFGAudit audit;
  if (storeIndex >= allInsns.size() || loadIndex >= allInsns.size() ||
      storeIndex >= loadIndex) {
    audit.unknownControlFlow = true;
    audit.reason = "invalid-store-load-order";
    return audit;
  }

  uint64_t storeOffset = allInsns[storeIndex].offset;
  uint64_t loadOffset = allInsns[loadIndex].offset;
  for (size_t i = storeIndex + 1; i < loadIndex; ++i) {
    const RISCVLibcInsn &insn = allInsns[i];
    if (!insn.supported) {
      audit.unknownControlFlow = true;
      audit.reason = "unsupported-instruction";
      continue;
    }
    if (riscvLibcInsnWritesReg(insn, 2)) {
      audit.spModified = true;
      audit.reason = "sp-modified";
    }
    if (insn.stackOffset == stackOffset &&
        (insn.stackMemKind == RISCVLibcStackMemKind::CSWSP ||
         insn.stackMemKind == RISCVLibcStackMemKind::SW)) {
      audit.sameSlotClobber = true;
      audit.reason = "same-slot-clobber";
    }
    if (!insn.controlFlow)
      continue;
    if (isRISCVLibcNormalDirectCall(controlFlowRelocs, insn))
      continue;
    if (isRISCVLibcReturn(insn))
      continue;
    const RISCVLibcControlFlowRelocInfo *target =
        getRISCVLibcDirectBranchTarget(controlFlowRelocs, insn);
    if (!target || !target->hasTarget) {
      audit.unknownControlFlow = true;
      audit.reason = "unknown-control-flow";
      continue;
    }
    if (target->targetSection != &sec)
      continue;
    if (target->targetOffset > storeOffset && target->targetOffset <= loadOffset &&
        target->targetOffset <= insn.offset)
      audit.backedgeBypass = true;
  }

  for (const auto &entry : controlFlowRelocs) {
    uint64_t sourceOffset = entry.first;
    for (const RISCVLibcControlFlowRelocInfo &r : entry.second) {
      if (r.type != R_RISCV_BRANCH && r.type != R_RISCV_JAL &&
          r.type != R_RISCV_RVC_BRANCH && r.type != R_RISCV_RVC_JUMP &&
          r.type != R_RISCV_CALL && r.type != R_RISCV_CALL_PLT)
        continue;
      if (!r.hasTarget || r.targetSection != &sec)
        continue;
      if (r.targetOffset > storeOffset && r.targetOffset <= loadOffset &&
          (sourceOffset <= storeOffset || sourceOffset > loadOffset)) {
        audit.externalEntry = true;
        if (sourceOffset > loadOffset)
          audit.backedgeBypass = true;
      }
    }
  }

  if (audit.sameSlotClobber)
    audit.reason = "same-slot-clobber";
  else if (audit.externalEntry)
    audit.reason = "external-entry";
  else if (audit.spModified)
    audit.reason = "sp-modified";
  else if (audit.backedgeBypass)
    audit.reason = "backedge-bypass";
  else if (audit.unknownControlFlow)
    audit.reason = "unknown-control-flow";
  else {
    audit.safe = true;
    audit.reason = "none";
  }
  return audit;
}

template <class ELFT>
static RISCVLibcRegDefDiag classifyRISCVLibcRegDef(
    InputSectionBase &sec, ArrayRef<RISCVLibcInsn> allInsns,
    size_t beforeIndex, int reg) {
  RISCVLibcRegDefDiag diag;
  for (size_t i = beforeIndex; i > 0; --i) {
    const RISCVLibcInsn &def = allInsns[i - 1];
    if (!riscvLibcInsnWritesReg(def, reg))
      continue;
    diag.offset = def.offset;
    if (def.addi) {
      DenseMap<uint64_t, RISCVLibcRelocTarget> relocTargets =
          getRISCVLibcRelocTargets<ELFT>(sec);
      auto loRel = relocTargets.find(def.offset);
      if (loRel != relocTargets.end() && loRel->second.absLoI && i >= 2) {
        const RISCVLibcInsn &hi = allInsns[i - 2];
        auto hiRel = relocTargets.find(hi.offset);
        if (hi.lui && hi.rd == def.rs1 && hiRel != relocTargets.end() &&
            hiRel->second.absHi && hiRel->second.sym == loRel->second.sym &&
            hiRel->second.addend == loRel->second.addend) {
          diag.kind = "constant-string";
          RISCVLibcCandidateFormat f;
          if (loRel->second.sym &&
              targetRISCVLibcCString(*loRel->second.sym,
                                     loRel->second.addend, f)) {
            diag.constantFormatProven = true;
            diag.format = f.text;
            diag.reason = "none";
          } else {
            diag.reason = "target-not-string";
          }
          return diag;
        }
      }
    }
    if (def.lui && i < allInsns.size()) {
      const RISCVLibcInsn &lo = allInsns[i];
      if (lo.addi && lo.rs1 == reg) {
        DenseMap<uint64_t, RISCVLibcRelocTarget> relocTargets =
            getRISCVLibcRelocTargets<ELFT>(sec);
        auto hiRel = relocTargets.find(def.offset);
        auto loRel = relocTargets.find(lo.offset);
        if (hiRel != relocTargets.end() && loRel != relocTargets.end() &&
            hiRel->second.absHi && loRel->second.lo &&
            hiRel->second.sym == loRel->second.sym &&
            hiRel->second.addend == loRel->second.addend) {
          diag.kind = "constant-string";
          RISCVLibcCandidateFormat f;
          if (loRel->second.sym &&
              targetRISCVLibcCString(*loRel->second.sym,
                                     loRel->second.addend, f)) {
            diag.constantFormatProven = true;
            diag.format = f.text;
            diag.reason = "none";
          } else {
            diag.reason = "target-not-string";
          }
          return diag;
        }
      }
    }
    if (def.copy && def.copySrc >= 0) {
      diag.kind = isRISCVIntegerCalleeSavedReg(def.copySrc)
                      ? "copy-from-callee-saved"
                      : "copy";
      diag.copySrc = def.copySrc;
      diag.copySrcIsCalleeSaved = isRISCVIntegerCalleeSavedReg(def.copySrc);
      if (!diag.copySrcIsCalleeSaved)
        return diag;

      RISCVLibcRegDefDiag srcDiag =
          classifyRISCVLibcRegDef<ELFT>(sec, allInsns, i - 1, def.copySrc);
      if (srcDiag.constantFormatProven) {
        diag.constantFormatProven = true;
        diag.format = srcDiag.format;
        diag.reason = "none";
      } else {
        diag.reason = srcDiag.reason.empty() ? srcDiag.kind : srcDiag.reason;
      }
      return diag;
    }
    if (isRISCVIntegerCalleeSavedReg(reg)) {
      diag.kind = "callee-saved-register";
      diag.reason = "callee-saved-source-not-locally-proven";
      return diag;
    }
    if (def.stackMemKind == RISCVLibcStackMemKind::CLWSP ||
        def.stackMemKind == RISCVLibcStackMemKind::LW) {
      diag.kind = "load";
      return diag;
    }
    if (def.controlFlow && def.call) {
      diag.kind = "call-result";
      return diag;
    }
    diag.kind = riscvLibcInsnKind(def).str();
    return diag;
  }
  if (isRISCVIntegerCalleeSavedReg(reg)) {
    diag.kind = "callee-saved-register";
    diag.reason = "callee-saved-source-not-locally-proven";
  }
  return diag;
}

template <class ELFT>
static bool dumpRISCVLibcStackSlotAudit(const RISCVLibcPrintfCall &call,
                                        const RISCVLibcFunctionDecode &decoded,
                                        const DenseMap<uint64_t,
                                                       SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
                                            &controlFlowRelocs,
                                        uint32_t &recognizedLoads,
                                        DenseSet<int64_t> &uniqueOffsets,
                                        uint32_t &nearestStoreFound,
                                        uint32_t &nearestStoreIsCSWSP,
                                        uint32_t &nearestStoreSrcCopy,
                                        uint32_t &nearestStoreCopyFromCalleeSaved,
                                        uint32_t &nearestStoreConstFormatProven,
                                        uint32_t &nearestStoreNotProven,
                                        uint32_t &cfgCandidates,
                                        uint32_t &storeDominatesLoad,
                                        uint32_t &noSameSlotClobber,
                                        uint32_t &spStable,
                                        uint32_t &noExternalEntry,
                                        uint32_t &noUnknownControlFlow,
                                        uint32_t &cfgSafe) {
  int formatReg = getRISCVPrintfFormatArgReg(call.target->getName());
  SmallVector<RISCVLibcInsn, 0> allInsns;
  std::string reason;
  if (!collectRISCVLibcInsnsBeforeCall(decoded, call.callOffset, allInsns,
                                       reason, UINT32_MAX))
    return false;

  const RISCVLibcInsn *load = nullptr;
  size_t loadIndex = 0;
  for (size_t i = allInsns.size(); i > 0; --i) {
    const RISCVLibcInsn &insn = allInsns[i - 1];
    if (!riscvLibcInsnWritesReg(insn, formatReg))
      continue;
    if ((insn.stackMemKind == RISCVLibcStackMemKind::CLWSP ||
         insn.stackMemKind == RISCVLibcStackMemKind::LW) &&
        insn.rs1 == 2) {
      load = &insn;
      loadIndex = i - 1;
    }
    break;
  }
  if (!load)
    return false;

  ++recognizedLoads;
  uniqueOffsets.insert(load->stackOffset);
  message(Twine("  printf_stack_slot_audit caller=") +
          call.caller->getName() + " target=" + call.target->getName() +
          " call_offset=" + hexOffset(call.callOffset) +
          " load_offset=" + hexOffset(load->offset) +
          " stack_offset=" + Twine(load->stackOffset) +
          " load_kind=" + riscvLibcStackMemKindToString(load->stackMemKind));

  const RISCVLibcInsn *nearestStore = nullptr;
  size_t nearestStoreIndex = 0;
  for (size_t i = loadIndex; i > 0; --i) {
    const RISCVLibcInsn &store = allInsns[i - 1];
    if (store.stackOffset != load->stackOffset ||
        (store.stackMemKind != RISCVLibcStackMemKind::CSWSP &&
         store.stackMemKind != RISCVLibcStackMemKind::SW))
      continue;
    nearestStore = &store;
    nearestStoreIndex = i - 1;
    break;
  }
  if (!nearestStore) {
    ++nearestStoreNotProven;
    message(Twine("  printf_stack_slot_nearest_store caller=") +
            call.caller->getName() +
            " call_offset=" + hexOffset(call.callOffset) +
            " load_offset=" + hexOffset(load->offset) +
            " stack_offset=" + Twine(load->stackOffset) +
            " store_offset=none store_kind=none store_src=none"
            " store_src_def_kind=none copy_src=none"
            " copy_src_is_callee_saved=0 constant_format_proven=0"
            " format=\"none\" reason=nearest-store-not-found");
    return true;
  }

  ++nearestStoreFound;
  ++cfgCandidates;
  if (nearestStore->stackMemKind == RISCVLibcStackMemKind::CSWSP)
    ++nearestStoreIsCSWSP;
  RISCVLibcRegDefDiag defDiag =
      classifyRISCVLibcRegDef<ELFT>(*call.sourceSection, allInsns,
                                    nearestStoreIndex,
                                    nearestStore->stackStoreSrc);
  if (defDiag.kind == "copy" || defDiag.kind == "copy-from-callee-saved")
    ++nearestStoreSrcCopy;
  if (defDiag.copySrcIsCalleeSaved)
    ++nearestStoreCopyFromCalleeSaved;
  if (defDiag.constantFormatProven)
    ++nearestStoreConstFormatProven;
  else
    ++nearestStoreNotProven;
  RISCVLibcStackSlotCFGAudit cfgAudit = auditRISCVLibcStackSlotCFG(
      *call.sourceSection, decoded, allInsns, nearestStoreIndex, loadIndex,
      controlFlowRelocs, load->stackOffset);
  if (!cfgAudit.externalEntry && !cfgAudit.backedgeBypass &&
      !cfgAudit.unknownControlFlow)
    ++storeDominatesLoad;
  if (!cfgAudit.sameSlotClobber)
    ++noSameSlotClobber;
  if (!cfgAudit.spModified)
    ++spStable;
  if (!cfgAudit.externalEntry)
    ++noExternalEntry;
  if (!cfgAudit.unknownControlFlow)
    ++noUnknownControlFlow;
  if (cfgAudit.safe)
    ++cfgSafe;

  message(Twine("  printf_stack_slot_nearest_store caller=") +
          call.caller->getName() +
          " call_offset=" + hexOffset(call.callOffset) +
          " load_offset=" + hexOffset(load->offset) +
          " stack_offset=" + Twine(load->stackOffset) +
          " store_offset=" + hexOffset(nearestStore->offset) +
          " store_kind=" +
          riscvLibcStackMemKindToString(nearestStore->stackMemKind) +
          " store_src=" + riscvLibcXRegName(nearestStore->stackStoreSrc) +
          " store_src_def_kind=" + defDiag.kind +
          " store_src_def_offset=" + hexOffsetOrNone(defDiag.offset) +
          " copy_src=" + riscvLibcXRegName(defDiag.copySrc) +
          " copy_src_is_callee_saved=" +
          Twine(defDiag.copySrcIsCalleeSaved ? 1 : 0) +
          " copy_offset=" +
          hexOffsetOrNone(defDiag.copySrc >= 0
                              ? defDiag.offset
                              : std::numeric_limits<uint64_t>::max()) +
          " constant_format_proven=" +
          Twine(defDiag.constantFormatProven ? 1 : 0) + " format=\"" +
          defDiag.format + "\" reason=" + defDiag.reason);
  message(Twine("  printf_stack_slot_cfg_audit call_offset=") +
          hexOffset(call.callOffset) +
          " store_offset=" + hexOffset(nearestStore->offset) +
          " load_offset=" + hexOffset(load->offset) +
          " stack_offset=" + Twine(load->stackOffset) +
          " same_slot_clobber=" + Twine(cfgAudit.sameSlotClobber ? 1 : 0) +
          " external_entry=" + Twine(cfgAudit.externalEntry ? 1 : 0) +
          " sp_modified=" + Twine(cfgAudit.spModified ? 1 : 0) +
          " backedge_bypass=" + Twine(cfgAudit.backedgeBypass ? 1 : 0) +
          " unknown_control_flow=" +
          Twine(cfgAudit.unknownControlFlow ? 1 : 0) +
          " cfg_safe=" + Twine(cfgAudit.safe ? 1 : 0) +
          " reason=" + cfgAudit.reason);
  return true;
}

template <class ELFT, class RelTy>
static void dumpRISCVLibcRelocAt(InputSectionBase &sec, const RelTy &rel) {
  Symbol &target = sec.getFile<ELFT>()->getRelocTargetSym(rel);
  Defined *d = dyn_cast<Defined>(&target);
  std::string targetSection = "none";
  if (d)
    if (auto *targetSec = dyn_cast_or_null<InputSectionBase>(d->section))
      targetSection = targetSec->name.str();

  std::string msg =
      (Twine("      reloc offset=") + hexOffset(rel.r_offset) +
       " type=" + lld::toString(rel.getType(config->isMips64EL)) +
       " target_symbol=" + target.getName() +
       " addend=" + Twine(getRISCVLibcAddend(rel)) +
       " target_section=" + targetSection)
          .str();
  if (d)
    msg = (Twine(msg) + " symbol_value=" + hexOffset(d->value) +
           " symbol_size=" + Twine(d->size))
              .str();
  message(msg);
}

template <class ELFT>
static void dumpRISCVLibcRelocsAt(InputSectionBase &sec, uint64_t off) {
  if (!sec.file)
    return;
  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  for (const auto &rel : rels.rels)
    if (rel.r_offset == off)
      dumpRISCVLibcRelocAt<ELFT>(sec, rel);
  for (const auto &rel : rels.relas)
    if (rel.r_offset == off)
      dumpRISCVLibcRelocAt<ELFT>(sec, rel);
}

template <class ELFT>
static std::string summarizeRISCVLibcRelocsAt(InputSectionBase &sec,
                                              uint64_t off) {
  if (!sec.file)
    return "none";
  SmallVector<std::string, 0> parts;
  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  auto collect = [&](auto rels) {
    for (const auto &rel : rels) {
      if (rel.r_offset != off)
        continue;
      Symbol &target = sec.getFile<ELFT>()->getRelocTargetSym(rel);
      parts.push_back((Twine(lld::toString(rel.getType(config->isMips64EL))) +
                       ":" + target.getName() + ":addend=" +
                       Twine(getRISCVLibcAddend(rel)))
                          .str());
    }
  };
  collect(rels.rels);
  collect(rels.relas);
  return parts.empty() ? std::string("none") : llvm::join(parts, ",");
}

template <class ELFT>
static void dumpRISCVLibcFailedCallsiteContext(
    const RISCVLibcPrintfCall &call, const RISCVLibcFunctionDecode &decoded) {
  int formatReg = getRISCVPrintfFormatArgReg(call.target->getName());
  message("    failed_callsite_context:");
  message(Twine("      format_reg=") + riscvLibcRegName(formatReg) +
          " reason=" + call.reason);

  SmallVector<RISCVLibcInsn, 0> insns;
  std::string decodeReason;
  if (!collectRISCVLibcInsnsBeforeCall(decoded, call.callOffset, insns,
                                       decodeReason, 24)) {
    if (decodeReason == "decode-did-not-reach-call-offset")
      message("      decode_did_not_reach_call_offset=1");
    else
      message("      decode_failed=1");
    return;
  }

  const RISCVLibcInsn *lastDef = nullptr;
  const RISCVLibcInsn *intermediateCall = nullptr;
  for (const RISCVLibcInsn &insn : insns) {
    if (riscvLibcInsnWritesReg(insn, formatReg))
      lastDef = &insn;
    if (insn.controlFlow && insn.call)
      intermediateCall = &insn;
  }

  if (lastDef) {
    message(Twine("      proof_state format_reg=") +
            riscvLibcRegName(formatReg) +
            " last_def_offset=" + hexOffset(lastDef->offset) +
            " last_def_rd=" + riscvLibcXRegName(lastDef->rd) +
            " last_def_rs1=" + riscvLibcXRegName(lastDef->rs1) +
            " last_def_rs2=" + riscvLibcXRegName(lastDef->rs2) +
            " last_def_kind=" + riscvLibcInsnKind(*lastDef) +
            " copySrc=" + riscvLibcXRegName(lastDef->copySrc));
  } else {
    message(Twine("      proof_state format_reg=") +
            riscvLibcRegName(formatReg) + " last_def_offset=none");
  }

  if (call.reason == "intermediate-call" && intermediateCall) {
    message(Twine("      intermediate_call_offset=") +
            hexOffset(intermediateCall->offset));
    dumpRISCVLibcRelocsAt<ELFT>(*call.sourceSection, intermediateCall->offset);
  }

  for (const RISCVLibcInsn &insn : insns) {
    message(Twine("      insn offset=") + hexOffset(insn.offset) +
            " size=" + Twine(insn.size) + " raw=" + hexOffset(insn.raw) +
            " opcode=" +
            hexOffset(insn.size == 4 ? (insn.raw & 0x7f) : (insn.raw & 0x3)) +
            " rd=" + riscvLibcXRegName(insn.rd) +
            " rs1=" + riscvLibcXRegName(insn.rs1) +
            " rs2=" + riscvLibcXRegName(insn.rs2) +
            " supported=" + Twine(insn.supported ? 1 : 0) +
            " control_flow=" + Twine(insn.controlFlow ? 1 : 0) +
            " call=" + Twine(insn.call ? 1 : 0) +
            " writesRd=" + Twine(insn.writesRd ? 1 : 0) +
            " writes_format_reg=" +
            Twine(riscvLibcInsnWritesReg(insn, formatReg) ? 1 : 0) +
            " reads_format_reg_rs1=" +
            Twine(insn.rs1 == formatReg ? 1 : 0) +
            " reads_format_reg_rs2=" +
            Twine(insn.rs2 == formatReg ? 1 : 0) +
            " kind=" + riscvLibcInsnKind(insn) +
            " copySrc=" + riscvLibcXRegName(insn.copySrc));
    dumpRISCVLibcRelocsAt<ELFT>(*call.sourceSection, insn.offset);
  }
}

template <class ELFT>
static bool proveRISCVLibcEntryCalleeSavedFormat(
    InputSectionBase &sec, const RISCVLibcFunctionDecode &decoded,
    uint64_t callOff, int argReg,
    ArrayRef<RISCVLibcInsn> insns,
    DenseMap<uint64_t, RISCVLibcRelocTarget> &relocTargets,
    RISCVLibcCandidateFormat &format, std::string &proof,
    std::string &reason, RISCVLibcEntryCalleeSavedDiag &diag) {
  if (argReg < 0)
    return false;

  const RISCVLibcInsn *copyInsn = nullptr;
  for (size_t i = insns.size(); i > 0; --i) {
    const RISCVLibcInsn &insn = insns[i - 1];
    if (!insn.supported) {
      reason = "unsupported-instruction";
      diag.reason = reason;
      return false;
    }
    if (riscvLibcInsnWritesReg(insn, argReg)) {
      copyInsn = &insn;
      break;
    }
  }
  if (!copyInsn || !copyInsn->copy ||
      !isRISCVIntegerCalleeSavedReg(copyInsn->copySrc)) {
    if (copyInsn) {
      diag.copyOffset = copyInsn->offset;
      diag.copySrc = copyInsn->copySrc;
    }
    reason = "entry-final-copy-not-callee-saved";
    diag.reason = reason;
    return false;
  }
  diag.copyOffset = copyInsn->offset;
  diag.copySrc = copyInsn->copySrc;

  for (const RISCVLibcInsn &insn : insns) {
    if (insn.offset <= copyInsn->offset)
      continue;
    if (!insn.supported) {
      reason = "unsupported-instruction";
      diag.reason = reason;
      return false;
    }
    if (insn.controlFlow) {
      reason = insn.call ? "intermediate-call" : "control-flow-boundary";
      diag.reason = reason;
      return false;
    }
    if (riscvLibcInsnWritesReg(insn, argReg)) {
      reason = "format-register-clobbered";
      diag.reason = reason;
      return false;
    }
  }

  SmallVector<RISCVLibcInsn, 0> allInsns;
  if (!collectRISCVLibcInsnsBeforeCall(decoded, callOff, allInsns, reason)) {
    diag.reason = reason;
    return false;
  }

  size_t prefixEnd = allInsns.size();
  for (auto [i, insn] : llvm::enumerate(allInsns)) {
    if (insn.controlFlow) {
      prefixEnd = i;
      diag.firstControlFlowOffset = insn.offset;
      diag.firstControlFlowKind = riscvLibcInsnKind(insn).str();
      diag.firstControlFlowRelocs =
          summarizeRISCVLibcRelocsAt<ELFT>(sec, insn.offset);
      diag.firstControlFlowRaw = insn.raw;
      if (insn.size == 2) {
        diag.firstControlFlowQuadrant = insn.raw & 0x3;
        diag.firstControlFlowFunct3 = (insn.raw >> 13) & 0x7;
      }
      break;
    }
  }
  diag.prefixEndOffset =
      prefixEnd == allInsns.size() ? callOff : allInsns[prefixEnd].offset;

  const RISCVLibcInsn *loInsn = nullptr;
  const RISCVLibcInsn *hiInsn = nullptr;
  for (size_t i = 0; i < prefixEnd; ++i) {
    const RISCVLibcInsn &insn = allInsns[i];
    if (!insn.supported) {
      reason = "unsupported-instruction";
      diag.reason = reason;
      return false;
    }
    if (!riscvLibcInsnWritesReg(insn, copyInsn->copySrc))
      continue;
    auto loRel = relocTargets.find(insn.offset);
    if (!insn.addi || loRel == relocTargets.end() || !loRel->second.lo)
      continue;
    for (size_t h = i; h > 0; --h) {
      const RISCVLibcInsn &prev = allInsns[h - 1];
      if (!prev.supported) {
        reason = "unsupported-instruction";
        diag.reason = reason;
        return false;
      }
      if (!riscvLibcInsnWritesReg(prev, insn.rs1))
        continue;
      auto hiRel = relocTargets.find(prev.offset);
      if (hiRel == relocTargets.end() ||
          hiRel->second.sym != loRel->second.sym ||
          hiRel->second.addend != loRel->second.addend) {
        diag.candidateHi = prev.offset;
        diag.candidateLo = insn.offset;
        diag.candidateDst = insn.rd;
        diag.candidateSymbol =
            loRel->second.sym ? loRel->second.sym->getName().str() : "none";
        diag.candidateRejectReason = "hi-lo-symbol-mismatch";
        break;
      }
      if (prev.lui && hiRel->second.absHi) {
        diag.candidateHi = prev.offset;
        diag.candidateLo = insn.offset;
        diag.candidateDst = insn.rd;
        diag.candidateSymbol =
            loRel->second.sym ? loRel->second.sym->getName().str() : "none";
        diag.candidateRejectReason = "accepted";
        loInsn = &insn;
        hiInsn = &prev;
      } else {
        diag.candidateHi = prev.offset;
        diag.candidateLo = insn.offset;
        diag.candidateDst = insn.rd;
        diag.candidateSymbol =
            loRel->second.sym ? loRel->second.sym->getName().str() : "none";
        diag.candidateRejectReason = "hi-not-absolute-lui";
      }
      break;
    }
    if (loInsn)
      break;
  }
  if (!loInsn || !hiInsn) {
    reason = "entry-callee-saved-init-not-found";
    diag.reason = reason;
    return false;
  }

  auto loRel = relocTargets.find(loInsn->offset);
  if (loRel == relocTargets.end() ||
      !targetRISCVLibcCString(*loRel->second.sym, loRel->second.addend, format)) {
    reason = "entry-callee-saved-target-not-string";
    diag.reason = reason;
    return false;
  }

  bool afterInit = false;
  for (const RISCVLibcInsn &insn : allInsns) {
    if (insn.offset == loInsn->offset) {
      afterInit = true;
      continue;
    }
    if (!afterInit || insn.offset >= copyInsn->offset)
      continue;
    if (!insn.supported) {
      reason = "unsupported-instruction";
      diag.reason = reason;
      return false;
    }
    if (riscvLibcInsnWritesReg(insn, copyInsn->copySrc)) {
      reason = "callee-saved-format-reg-clobbered";
      diag.reason = reason;
      return false;
    }
  }

  proof = (Twine("ENTRY_CONST_CALLEE_SAVED_COPY_") +
           riscvLibcSRegName(copyInsn->copySrc))
              .str();
  diag.reason = "accepted";
  return true;
}

static std::string
formatRISCVLibcEntryCalleeSavedDiag(const RISCVLibcEntryCalleeSavedDiag &d) {
  return (Twine("entry_prefix_end_offset=") + hexOffsetOrNone(d.prefixEndOffset) +
          " entry_first_control_flow_offset=" +
          hexOffsetOrNone(d.firstControlFlowOffset) +
          " entry_first_control_flow_kind=" + d.firstControlFlowKind +
          " entry_first_control_flow_raw=" +
          (d.firstControlFlowOffset == std::numeric_limits<uint64_t>::max()
               ? std::string("none")
               : hexOffset(d.firstControlFlowRaw)) +
          " entry_first_control_flow_quadrant=" +
          (d.firstControlFlowQuadrant < 0
               ? std::string("none")
               : Twine(d.firstControlFlowQuadrant).str()) +
          " entry_first_control_flow_funct3=" +
          (d.firstControlFlowFunct3 < 0 ? std::string("none")
                                        : Twine(d.firstControlFlowFunct3).str()) +
          " entry_first_control_flow_relocs=" + d.firstControlFlowRelocs +
          " entry_copy_offset=" + hexOffsetOrNone(d.copyOffset) +
          " entry_copy_src=" + riscvLibcXRegName(d.copySrc) +
          " entry_copy_src_is_callee_saved=" +
          Twine(isRISCVIntegerCalleeSavedReg(d.copySrc) ? 1 : 0) +
          " entry_init_candidate_hi=" + hexOffsetOrNone(d.candidateHi) +
          " entry_init_candidate_lo=" + hexOffsetOrNone(d.candidateLo) +
          " entry_init_candidate_dst=" + riscvLibcXRegName(d.candidateDst) +
          " entry_init_candidate_symbol=" + d.candidateSymbol +
          " entry_init_reject_reason=" + d.candidateRejectReason)
      .str();
}

static std::string
formatRISCVLibcLocalDominatingDiag(const RISCVLibcLocalDominatingDiag &d) {
  std::string out =
      (Twine("local_copy_offset=") + hexOffsetOrNone(d.copyOffset) +
       " local_copy_src=" + riscvLibcXRegName(d.copySrc) +
       " local_nearest_def_offset=" + hexOffsetOrNone(d.nearestDefOffset) +
       " local_hi_offset=" + hexOffsetOrNone(d.hiOffset) +
       " local_lo_offset=" + hexOffsetOrNone(d.loOffset) +
       " local_init_start=" + hexOffsetOrNone(d.initStart) +
       " local_init_complete=" + hexOffsetOrNone(d.initComplete))
          .str();
  if (d.externalEntrySource != std::numeric_limits<uint64_t>::max())
    out += " local_external_entry_source=" +
           hexOffset(d.externalEntrySource);
  if (d.externalEntryTarget != std::numeric_limits<uint64_t>::max())
    out += " local_external_entry_target=" +
           hexOffset(d.externalEntryTarget);
  if (d.unknownControlFlowOffset != std::numeric_limits<uint64_t>::max())
    out += " local_unknown_control_flow_offset=" +
           hexOffset(d.unknownControlFlowOffset);
  return out;
}

static std::string
formatRISCVLibcLoopCarriedDiag(const RISCVLibcLoopCarriedDiag &d) {
  std::string out =
      (Twine("loop_region_start=") + hexOffsetOrNone(d.regionStart) +
       " loop_region_end=" + hexOffsetOrNone(d.regionEnd) +
       " loop_backedge_source=" + hexOffsetOrNone(d.backedgeSource) +
       " loop_backedge_target=" + hexOffsetOrNone(d.backedgeTarget))
          .str();
  if (d.externalEntrySource != std::numeric_limits<uint64_t>::max())
    out += " loop_external_entry_source=" +
           hexOffset(d.externalEntrySource);
  if (d.externalEntryTarget != std::numeric_limits<uint64_t>::max())
    out += " loop_external_entry_target=" +
           hexOffset(d.externalEntryTarget);
  if (d.unknownControlFlowOffset != std::numeric_limits<uint64_t>::max())
    out += " loop_unknown_control_flow_offset=" +
           hexOffset(d.unknownControlFlowOffset);
  return out;
}

static bool proveRISCVLibcDirectAbsFormatArg(
    int argReg, ArrayRef<RISCVLibcInsn> insns,
    DenseMap<uint64_t, RISCVLibcRelocTarget> &relocTargets,
    RISCVLibcCandidateFormat &format, std::string &proof,
    std::string &reason) {
  for (size_t i = insns.size(); i > 0; --i) {
    const RISCVLibcInsn &lo = insns[i - 1];
    if (!lo.supported) {
      reason = "unsupported-instruction";
      return false;
    }
    if (!riscvLibcInsnWritesReg(lo, argReg))
      continue;
    if (!lo.addi || lo.rs1 != argReg) {
      reason = "direct-abs-final-def-not-addi";
      return false;
    }
    auto loRel = relocTargets.find(lo.offset);
    if (loRel == relocTargets.end() || !loRel->second.absLoI) {
      reason = "direct-abs-lo12-not-found";
      return false;
    }
    if (i < 2) {
      reason = "direct-abs-hi20-not-adjacent";
      return false;
    }
    const RISCVLibcInsn &hi = insns[i - 2];
    if (!hi.supported) {
      reason = "unsupported-instruction";
      return false;
    }
    if (!hi.lui || !riscvLibcInsnWritesReg(hi, argReg)) {
      reason = "direct-abs-hi20-not-adjacent-lui";
      return false;
    }
    auto hiRel = relocTargets.find(hi.offset);
    if (hiRel == relocTargets.end() || !hiRel->second.absHi) {
      reason = "direct-abs-hi20-reloc-not-found";
      return false;
    }
    if (hiRel->second.sym != loRel->second.sym ||
        hiRel->second.addend != loRel->second.addend) {
      reason = "direct-abs-hi-lo-symbol-mismatch";
      return false;
    }
    for (size_t j = i; j < insns.size(); ++j) {
      const RISCVLibcInsn &mid = insns[j];
      if (!mid.supported) {
        reason = "unsupported-instruction";
        return false;
      }
      if (mid.controlFlow) {
        reason = mid.call ? "intermediate-call" : "control-flow-boundary";
        return false;
      }
      if (riscvLibcInsnWritesReg(mid, argReg)) {
        reason = "format-register-clobbered";
        return false;
      }
    }
    if (!targetRISCVLibcCString(*loRel->second.sym, loRel->second.addend,
                                format)) {
      reason = "direct-abs-target-not-string";
      return false;
    }
    proof = "DIRECT_ABS_FORMAT_ARG";
    return true;
  }
  return false;
}

static bool findRISCVLibcCalleeSavedConstCandidate(
    int argReg, ArrayRef<RISCVLibcInsn> windowInsns,
    const RISCVLibcFunctionDecode &decoded,
    DenseMap<uint64_t, RISCVLibcRelocTarget> &relocTargets,
    RISCVLibcCandidateFormat &format,
    RISCVLibcCalleeSavedConstCandidate &candidate,
    RISCVLibcLocalDominatingDiag *localDiag, std::string &reason) {
  auto fail = [&](StringRef why) {
    reason = why.str();
    if (localDiag)
      localDiag->reason = reason;
    return false;
  };

  const RISCVLibcInsn *copyInsn = nullptr;
  for (size_t i = windowInsns.size(); i > 0; --i) {
    const RISCVLibcInsn &insn = windowInsns[i - 1];
    if (!insn.supported)
      return fail("unsupported-instruction");
    if (riscvLibcInsnWritesReg(insn, argReg)) {
      copyInsn = &insn;
      break;
    }
  }
  if (copyInsn && localDiag) {
    localDiag->copyOffset = copyInsn->offset;
    localDiag->copySrc = copyInsn->copySrc;
  }
  if (!copyInsn || !copyInsn->copy ||
      !isRISCVIntegerCalleeSavedReg(copyInsn->copySrc))
    return fail("local-callee-saved-final-copy-not-found");

  for (const RISCVLibcInsn &insn : windowInsns) {
    if (insn.offset <= copyInsn->offset)
      continue;
    if (!insn.supported)
      return fail("unsupported-instruction");
    if (insn.controlFlow)
      return fail(insn.call ? "intermediate-call" : "control-flow-boundary");
    if (riscvLibcInsnWritesReg(insn, argReg))
      return fail("format-register-clobbered");
  }

  const RISCVLibcInsn *loInsn = nullptr;
  size_t loIndex = 0;
  for (size_t i = decoded.instructions.size(); i > 0; --i) {
    const RISCVLibcInsn &insn = decoded.instructions[i - 1];
    if (insn.offset >= copyInsn->offset)
      continue;
    if (!insn.supported)
      return fail("unsupported-instruction");
    if (!riscvLibcInsnWritesReg(insn, copyInsn->copySrc))
      continue;
    loInsn = &insn;
    if (localDiag)
      localDiag->nearestDefOffset = insn.offset;
    loIndex = i - 1;
    break;
  }
  if (!loInsn)
    return fail("local-callee-saved-init-not-found");

  auto loRel = relocTargets.find(loInsn->offset);
  if (!loInsn->addi || loInsn->rd != copyInsn->copySrc ||
      loRel == relocTargets.end() || !loRel->second.absLoI)
    return fail("local-callee-saved-nearest-def-not-constant");
  if (loIndex == 0)
    return fail("local-callee-saved-nearest-def-not-constant");
  const RISCVLibcInsn *hiInsn = &decoded.instructions[loIndex - 1];
  if (localDiag) {
    localDiag->hiOffset = hiInsn->offset;
    localDiag->loOffset = loInsn->offset;
  }
  auto hiRel = relocTargets.find(hiInsn->offset);
  if (hiInsn->offset + hiInsn->size != loInsn->offset ||
      !hiInsn->supported || !hiInsn->lui ||
      !riscvLibcInsnWritesReg(*hiInsn, loInsn->rs1) ||
      hiRel == relocTargets.end() || !hiRel->second.absHi ||
      hiRel->second.sym != loRel->second.sym ||
      hiRel->second.addend != loRel->second.addend)
    return fail("local-callee-saved-nearest-def-not-constant");
  if (!targetRISCVLibcCString(*loRel->second.sym, loRel->second.addend,
                              format))
    return fail("local-callee-saved-target-not-string");

  candidate.copyInsn = copyInsn;
  candidate.hiInsn = hiInsn;
  candidate.loInsn = loInsn;
  candidate.savedReg = copyInsn->copySrc;
  return true;
}

template <class ELFT>
static bool proveRISCVLibcLocalDominatingCalleeSavedConst(
    InputSectionBase &sec, int argReg, ArrayRef<RISCVLibcInsn> windowInsns,
    const RISCVLibcFunctionDecode &decoded,
    DenseMap<uint64_t, RISCVLibcRelocTarget> &relocTargets,
    DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &controlFlowRelocs,
    RISCVLibcCandidateFormat &format, std::string &proof,
    std::string &reason, RISCVLibcLocalDominatingDiag &diag) {
  auto fail = [&](StringRef why) {
    reason = why.str();
    diag.reason = reason;
    return false;
  };
  RISCVLibcCalleeSavedConstCandidate candidate;
  if (!findRISCVLibcCalleeSavedConstCandidate(argReg, windowInsns, decoded,
                                              relocTargets, format, candidate,
                                              &diag, reason))
    return false;
  const RISCVLibcInsn *copyInsn = candidate.copyInsn;
  const RISCVLibcInsn *loInsn = candidate.loInsn;
  const RISCVLibcInsn *hiInsn = candidate.hiInsn;

  uint64_t initStart = hiInsn->offset;
  uint64_t initComplete = loInsn->offset;
  uint64_t copyOffset = copyInsn->offset;
  diag.initStart = initStart;
  diag.initComplete = initComplete;

  if (hasRISCVLibcExternalEntryToProtectedInterval(
          sec, controlFlowRelocs, initStart, copyOffset, &diag))
    return fail("local-callee-saved-external-entry");

  for (const RISCVLibcInsn &insn : decoded.instructions) {
    if (insn.offset <= initComplete)
      continue;
    if (insn.offset >= copyOffset)
      break;
    if (!insn.supported)
      return fail("unsupported-instruction");
    if (riscvLibcInsnWritesReg(insn, copyInsn->copySrc))
      return fail("local-callee-saved-clobbered");
    if (!insn.controlFlow)
      continue;
    if (isRISCVLibcNormalDirectCall(controlFlowRelocs, insn))
      continue;
    if (isRISCVLibcReturn(insn))
      continue;
    const RISCVLibcControlFlowRelocInfo *target =
        getRISCVLibcDirectBranchTarget(controlFlowRelocs, insn);
    if (!target || !target->hasTarget) {
      diag.unknownControlFlowOffset = insn.offset;
      return fail("local-callee-saved-unknown-control-flow");
    }
  }

  for (const RISCVLibcInsn &insn : decoded.instructions) {
    if (!insn.controlFlow)
      continue;
    if (isRISCVLibcNormalDirectCall(controlFlowRelocs, insn))
      continue;
    if (isRISCVLibcReturn(insn))
      continue;
    const RISCVLibcControlFlowRelocInfo *target =
        getRISCVLibcDirectBranchTarget(controlFlowRelocs, insn);
    if (!target) {
      if (insn.offset > initComplete && insn.offset < copyOffset) {
        diag.unknownControlFlowOffset = insn.offset;
        return fail("local-callee-saved-unknown-control-flow");
      }
      continue;
    }
    if (!target->hasTarget) {
      if (insn.offset > initComplete && insn.offset < copyOffset) {
        diag.unknownControlFlowOffset = insn.offset;
        return fail("local-callee-saved-unknown-control-flow");
      }
      continue;
    }
    if (target->targetSection != &sec)
      continue;
    if (target->targetOffset > initStart && target->targetOffset <= copyOffset &&
        (insn.offset <= initStart || insn.offset > copyOffset)) {
      diag.externalEntrySource = insn.offset;
      diag.externalEntryTarget = target->targetOffset;
      return fail("local-callee-saved-external-entry");
    }
  }
  proof = (Twine("LOCAL_DOMINATING_CALLEE_SAVED_CONST_") +
           riscvLibcSRegName(copyInsn->copySrc))
              .str();
  diag.reason = "accepted";
  return true;
}

static bool proveRISCVLibcLoopCarriedCalleeSavedConst(
    InputSectionBase &sec, int argReg, ArrayRef<RISCVLibcInsn> windowInsns,
    const RISCVLibcFunctionDecode &decoded,
    DenseMap<uint64_t, RISCVLibcRelocTarget> &relocTargets,
    DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &controlFlowRelocs,
    RISCVLibcCandidateFormat &format, std::string &proof,
    std::string &reason, RISCVLibcLoopCarriedDiag &diag) {
  auto fail = [&](StringRef why) {
    reason = why.str();
    diag.reason = reason;
    return false;
  };

  RISCVLibcCalleeSavedConstCandidate candidate;
  std::string candidateReason;
  if (!findRISCVLibcCalleeSavedConstCandidate(argReg, windowInsns, decoded,
                                              relocTargets, format, candidate,
                                              nullptr, candidateReason))
    return fail(candidateReason);

  uint64_t initStart = candidate.hiInsn->offset;
  uint64_t initComplete = candidate.loInsn->offset;
  uint64_t copyOffset = candidate.copyInsn->offset;
  if (initStart < decoded.funcStart || initComplete < decoded.funcStart ||
      copyOffset < decoded.funcStart || initStart >= decoded.funcEnd ||
      initComplete >= decoded.funcEnd || copyOffset >= decoded.funcEnd ||
      copyOffset >= decoded.decodedEnd)
    return fail("loop-carried-unknown-control-flow");

  DenseSet<uint64_t> decodedInsnOffsets;
  decodedInsnOffsets.reserve(decoded.instructions.size());
  for (const RISCVLibcInsn &insn : decoded.instructions)
    decodedInsnOffsets.insert(insn.offset);
  if (!decodedInsnOffsets.contains(initStart) ||
      !decodedInsnOffsets.contains(initComplete) ||
      !decodedInsnOffsets.contains(copyOffset))
    return fail("loop-carried-unknown-control-flow");

  uint64_t regionStart = initStart;
  uint64_t regionEnd = copyOffset;
  bool sawBackedge = false;

  bool changed = true;
  while (changed) {
    changed = false;
    for (const auto &entry : controlFlowRelocs) {
      uint64_t sourceOffset = entry.first;
      for (const RISCVLibcControlFlowRelocInfo &r : entry.second) {
        if (r.type != R_RISCV_BRANCH && r.type != R_RISCV_JAL &&
            r.type != R_RISCV_RVC_BRANCH && r.type != R_RISCV_RVC_JUMP)
          continue;
        if (!r.hasTarget || r.targetSection != &sec)
          continue;
        if (sourceOffset > regionEnd && r.targetOffset > initComplete &&
            r.targetOffset <= regionEnd) {
          if (sourceOffset < decoded.funcStart ||
              sourceOffset >= decoded.funcEnd ||
              sourceOffset >= decoded.decodedEnd ||
              r.targetOffset < decoded.funcStart ||
              r.targetOffset >= decoded.funcEnd ||
              r.targetOffset >= decoded.decodedEnd ||
              !decodedInsnOffsets.contains(sourceOffset) ||
              !decodedInsnOffsets.contains(r.targetOffset)) {
            diag.unknownControlFlowOffset = sourceOffset;
            return fail("loop-carried-unknown-control-flow");
          }
          sawBackedge = true;
          diag.backedgeSource = sourceOffset;
          diag.backedgeTarget = r.targetOffset;
          regionEnd = sourceOffset;
          changed = true;
        }
      }
    }
  }

  diag.regionStart = regionStart;
  diag.regionEnd = regionEnd;
  if (!sawBackedge)
    return fail("loop-carried-external-entry");
  if (regionEnd < decoded.funcStart || regionEnd >= decoded.funcEnd ||
      regionEnd >= decoded.decodedEnd)
    return fail("loop-carried-unknown-control-flow");

  for (const auto &entry : controlFlowRelocs) {
    uint64_t sourceOffset = entry.first;
    for (const RISCVLibcControlFlowRelocInfo &r : entry.second) {
      if (r.type != R_RISCV_BRANCH && r.type != R_RISCV_JAL &&
          r.type != R_RISCV_RVC_BRANCH && r.type != R_RISCV_RVC_JUMP &&
          r.type != R_RISCV_CALL && r.type != R_RISCV_CALL_PLT)
        continue;
      if (!r.hasTarget || r.targetSection != &sec)
        continue;
      if (r.targetOffset > initStart && r.targetOffset <= regionEnd &&
          (sourceOffset <= initStart || sourceOffset > regionEnd)) {
        diag.externalEntrySource = sourceOffset;
        diag.externalEntryTarget = r.targetOffset;
        return fail("loop-carried-external-entry");
      }
    }
  }

  for (const RISCVLibcInsn &insn : decoded.instructions) {
    if (insn.offset <= initComplete)
      continue;
    if (insn.offset > regionEnd)
      break;
    if (!insn.supported)
      return fail("unsupported-instruction");
    if (riscvLibcInsnWritesReg(insn, candidate.savedReg))
      return fail("loop-carried-callee-saved-clobbered");
    if (!insn.controlFlow)
      continue;
    if (isRISCVLibcNormalDirectCall(controlFlowRelocs, insn))
      continue;
    if (isRISCVLibcReturn(insn))
      continue;
    const RISCVLibcControlFlowRelocInfo *target =
        getRISCVLibcDirectBranchTarget(controlFlowRelocs, insn);
    if (!target || !target->hasTarget) {
      diag.unknownControlFlowOffset = insn.offset;
      return fail("loop-carried-unknown-control-flow");
    }
  }

  proof = (Twine("LOOP_CARRIED_CALLEE_SAVED_CONST_") +
           riscvLibcSRegName(candidate.savedReg))
              .str();
  reason = "accepted";
  diag.reason = "accepted";
  return true;
}

template <class ELFT>
static bool proveRISCVLibcCallsiteFormat(
    InputSectionBase &sec, const RISCVLibcFunctionDecode &decoded,
    uint64_t callOff, int argReg,
    DenseMap<uint64_t, RISCVLibcRelocTarget> &relocTargets,
    DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &controlFlowRelocs,
    RISCVLibcCandidateFormat &format, std::string &proof, std::string &reason,
    std::string &entryReason, std::string &entryDetail,
    std::string &localDominatingReason,
    std::string &localDominatingDetail, std::string &loopCarriedReason,
    std::string &loopCarriedDetail) {
  if (argReg < 0) {
    reason = "unsupported-printf-family-target";
    return false;
  }
  if (callOff > sec.content().size()) {
    reason = "call-offset-out-of-range";
    return false;
  }
  constexpr uint32_t maxWindowInsns = 16;
  SmallVector<RISCVLibcInsn, 0> insns;
  if (!collectRISCVLibcInsnsBeforeCall(decoded, callOff, insns, reason,
                                       maxWindowInsns))
    return false;
  if (insns.empty()) {
    reason = "empty-call-window";
    return false;
  }

  if (proveRISCVLibcDirectAbsFormatArg(argReg, insns, relocTargets, format,
                                       proof, reason))
    return true;

  RISCVLibcEntryCalleeSavedDiag entryDiag;
  if (proveRISCVLibcEntryCalleeSavedFormat<ELFT>(
          sec, decoded, callOff, argReg, insns, relocTargets, format, proof,
          reason, entryDiag)) {
    entryReason = entryDiag.reason;
    entryDetail = formatRISCVLibcEntryCalleeSavedDiag(entryDiag);
    return true;
  }
  entryReason = entryDiag.reason;
  entryDetail = formatRISCVLibcEntryCalleeSavedDiag(entryDiag);

  RISCVLibcLocalDominatingDiag localDiag;
  if (proveRISCVLibcLocalDominatingCalleeSavedConst<ELFT>(
          sec, argReg, insns, decoded, relocTargets, controlFlowRelocs, format,
          proof, localDominatingReason, localDiag)) {
    localDominatingDetail = formatRISCVLibcLocalDominatingDiag(localDiag);
    return true;
  }
  localDominatingReason = localDiag.reason;
  localDominatingDetail = formatRISCVLibcLocalDominatingDiag(localDiag);

  if (localDominatingReason == "local-callee-saved-external-entry") {
    RISCVLibcLoopCarriedDiag loopDiag;
    if (proveRISCVLibcLoopCarriedCalleeSavedConst(
            sec, argReg, insns, decoded, relocTargets, controlFlowRelocs,
            format, proof, loopCarriedReason, loopDiag)) {
      loopCarriedDetail = formatRISCVLibcLoopCarriedDiag(loopDiag);
      return true;
    }
    loopCarriedReason = loopDiag.reason;
    loopCarriedDetail = formatRISCVLibcLoopCarriedDiag(loopDiag);
  }

  for (size_t i = insns.size(); i > 0; --i) {
    const RISCVLibcInsn &def = insns[i - 1];
    if (!def.supported) {
      reason = "unsupported-instruction";
      return false;
    }
    if (!riscvLibcInsnWritesReg(def, argReg))
      continue;

    auto checkRegBetween = [&](int reg, size_t begin, size_t end) {
      for (size_t j = begin; j < end; ++j) {
        const RISCVLibcInsn &mid = insns[j];
        if (!mid.supported) {
          reason = "unsupported-instruction";
          return false;
        }
        if (mid.controlFlow) {
          reason = mid.call ? "intermediate-call" : "control-flow-boundary";
          return false;
        }
        if (riscvLibcInsnWritesReg(mid, reg)) {
          reason = reg == argReg ? "format-register-clobbered"
                                 : "copy-source-clobbered";
          return false;
        }
      }
      return true;
    };

    if (def.copy && def.copySrc >= 0) {
      // ADDI arg, tmp, 0 or C.MV arg, tmp.
      for (size_t k = i - 1; k > 0; --k) {
        const RISCVLibcInsn &lo = insns[k - 1];
        if (!lo.supported) {
          reason = "unsupported-instruction";
          return false;
        }
        if (!riscvLibcInsnWritesReg(lo, def.copySrc))
          continue;
        if (!checkRegBetween(def.copySrc, k, i - 1) ||
            !checkRegBetween(argReg, i, insns.size()))
          return false;
        auto loRel = relocTargets.find(lo.offset);
        if (!lo.addi || lo.rs1 != def.copySrc || loRel == relocTargets.end() ||
            !loRel->second.lo) {
          reason = "unsupported-copy-source";
          return false;
        }
        for (size_t h = k - 1; h > 0; --h) {
          const RISCVLibcInsn &hi = insns[h - 1];
          if (!hi.supported) {
            reason = "unsupported-instruction";
            return false;
          }
          if (!riscvLibcInsnWritesReg(hi, def.copySrc))
            continue;
          if (!checkRegBetween(def.copySrc, h, k - 1))
            return false;
          auto hiRel = relocTargets.find(hi.offset);
          if (hiRel == relocTargets.end() ||
              hiRel->second.sym != loRel->second.sym ||
              hiRel->second.addend != loRel->second.addend) {
            reason = "copy-hi-lo-symbol-mismatch";
            return false;
          }
          if (hi.lui && hiRel->second.absHi &&
              targetRISCVLibcCString(*loRel->second.sym, loRel->second.addend,
                                     format)) {
            proof = "LUI_ADDI_COPY_A" + Twine(argReg - 10).str();
            return true;
          }
          if (hi.auipc && hiRel->second.pcrelHi) {
            reason = "pcrel-proof-disabled";
            return false;
          }
          reason = "unsupported-copy-hi-instruction";
          return false;
        }
        reason = "copy-hi-reloc-not-found";
        return false;
      }
      reason = "copy-source-not-found";
      return false;
    }

    auto defRel = relocTargets.find(def.offset);
    if (def.addi && def.rs1 == argReg && defRel != relocTargets.end() &&
        defRel->second.lo) {
      for (size_t k = i - 1; k > 0; --k) {
        const RISCVLibcInsn &prev = insns[k - 1];
        if (!prev.supported) {
          reason = "unsupported-instruction";
          return false;
        }
        if (!riscvLibcInsnWritesReg(prev, argReg))
          continue;
        if (!checkRegBetween(argReg, k, i - 1) ||
            !checkRegBetween(argReg, i, insns.size()))
          return false;
        auto prevRel = relocTargets.find(prev.offset);
        if (prevRel == relocTargets.end() ||
            prevRel->second.sym != defRel->second.sym ||
            prevRel->second.addend != defRel->second.addend) {
          reason = "hi-lo-symbol-mismatch";
          return false;
        }
        if (prev.lui && prevRel->second.absHi &&
            targetRISCVLibcCString(*defRel->second.sym, defRel->second.addend,
                                   format)) {
          proof = "LUI_ADDI_A" + Twine(argReg - 10).str();
          return true;
        }
        if (prev.auipc && prevRel->second.pcrelHi) {
          reason = "pcrel-proof-disabled";
          return false;
        }
        reason = "unsupported-hi-instruction";
        return false;
      }
      reason = "hi-reloc-not-found";
      return false;
    }

    reason = "unsupported-format-definition";
    return false;
  }

  reason = "format-register-definition-not-found";
  return false;
}

template <class ELFT>
static void collectRISCVLibcCandidateFormats(
    InputSectionBase &sec, Defined &caller,
    SmallVectorImpl<RISCVLibcCandidateFormat> &formats) {
  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  auto scan = [&](auto rels) {
    if (!sec.file)
      return;
    for (const auto &rel : rels) {
      Defined *fromFunc = sec.getEnclosingFunction(rel.r_offset);
      if (fromFunc != &caller)
        continue;
      Symbol &target = sec.getFile<ELFT>()->getRelocTargetSym(rel);
      Defined *d = dyn_cast<Defined>(&target);
      if (!d)
        continue;
      auto *targetSec = dyn_cast_or_null<InputSectionBase>(d->section);
      if (!targetSec || !isRISCVLibcReadOnlyData(*targetSec))
        continue;
      int64_t addend = getRISCVLibcAddend(rel);
      uint64_t off = 0;
      if (!checkedAddend(d->value, addend, off))
        continue;
      std::string text;
      if (!readCStringAt(*targetSec, off, text) || text.find('%') == text.npos)
        continue;
      RISCVLibcCandidateFormat f;
      f.text = std::move(text);
      scanPrintfFormat(f.text, f.hasFloat, f.hasLongDouble);
      if (!llvm::any_of(formats, [&](const RISCVLibcCandidateFormat &old) {
            return old.text == f.text;
          }))
        formats.push_back(std::move(f));
    }
  };
  scan(rels.rels);
  scan(rels.relas);
}

static bool
isRISCVLibcAuditSectionEligible(InputSectionBase *sec,
                                RISCVLibcAuditReachabilityMode mode) {
  if (!sec || sec == &InputSection::discarded || !sec->file)
    return false;
  if (!(sec->flags & SHF_ALLOC))
    return false;
  return mode == RISCVLibcAuditReachabilityMode::PreGCConservative ||
         sec->isLive();
}

template <class ELFT>
static void collectRISCVLibcAuditGraph(
    RISCVLibcAuditReachabilityMode mode,
    SmallVectorImpl<RISCVLibcFunctionNode> &nodes,
    DenseMap<Defined *, unsigned> &nodeIndex,
    SmallVectorImpl<RISCVLibcPrintfCall> &printfCalls,
    RISCVLibcPrintfCallCollectionStats &callStats,
    std::map<std::pair<InputSectionBase *, Defined *>,
             RISCVLibcFunctionDecode> &decodeCache,
    std::map<InputSectionBase *, DenseMap<uint64_t, RISCVLibcRelocTarget>>
        &relocTargetCache,
    std::map<InputSectionBase *,
             DenseMap<uint64_t,
                      SmallVector<RISCVLibcControlFlowRelocInfo, 0>>>
        &controlFlowRelocCache,
    RISCVLibcAuditPerfStats &perfStats) {
  for (ELFFileBase *file : ctx.objectFiles) {
    for (Symbol *sym : file->getSymbols()) {
      Defined *d = dyn_cast_or_null<Defined>(sym);
      if (!d || d->type != STT_FUNC)
        continue;
      auto *sec = dyn_cast_or_null<InputSectionBase>(d->section);
      if (!isRISCVLibcAuditSectionEligible(sec, mode))
        continue;
      unsigned idx = nodes.size();
      RISCVLibcFunctionNode node;
      node.sym = d;
      node.section = sec;
      node.size = d->size;
      nodes.push_back(std::move(node));
      nodeIndex.try_emplace(d, idx);
    }
  }

  std::set<std::tuple<InputSectionBase *, uint64_t, Defined *>>
      seenPrintfCallsites;

  auto recordRel = [&](InputSectionBase &sec, auto rels) {
    if (!isRISCVLibcAuditSectionEligible(&sec, mode))
      return;
    for (const auto &rel : rels) {
      RelType type = rel.getType(config->isMips64EL);
      Symbol &targetSym = sec.getFile<ELFT>()->getRelocTargetSym(rel);
      Defined *target = dyn_cast<Defined>(&targetSym);
      if (!target || target->type != STT_FUNC)
        continue;
      auto targetIt = nodeIndex.find(target);
      if (targetIt == nodeIndex.end())
        continue;
      Defined *sourceFunc = nullptr;
      if (sec.flags & SHF_EXECINSTR)
        sourceFunc = sec.getEnclosingFunction(rel.r_offset);
      auto sourceIt = sourceFunc ? nodeIndex.find(sourceFunc) : nodeIndex.end();
      RISCVLibcRefKind kind = classifyRISCVLibcRef(type);

      RISCVLibcIncomingRef incoming;
      incoming.sourceFunction = sourceFunc;
      incoming.sourceSection = &sec;
      incoming.sourceLive = sec.isLive();
      incoming.type = type;
      incoming.kind = kind;
      nodes[targetIt->second].incoming.push_back(incoming);

      if (sourceIt != nodeIndex.end()) {
        SmallVector<unsigned, 0> &callees = nodes[sourceIt->second].callees;
        if (!llvm::is_contained(callees, targetIt->second))
          callees.push_back(targetIt->second);
      }

      if (isPrintfFamilyName(target->getName()) &&
          kind == RISCVLibcRefKind::DirectCall && sourceFunc &&
          sourceIt != nodeIndex.end()) {
        ++callStats.rawPrintfDirectCallRecords;
        if (!seenPrintfCallsites.insert({&sec, rel.r_offset, target}).second) {
          ++callStats.duplicatePrintfDirectCallRecords;
          continue;
        }
        RISCVLibcPrintfCall call;
        call.caller = sourceFunc;
        call.sourceSection = &sec;
        call.target = target;
        call.type = type;
        call.callOffset = rel.r_offset;
        collectRISCVLibcCandidateFormats<ELFT>(sec, *sourceFunc,
                                               call.candidateFormats);
        if (isRISCVPrintfInternalForwarder(sourceFunc->getName(),
                                           target->getName())) {
          call.formatClass = RISCVLibcFormatClass::InternalForwarder;
          call.reason = "recognized-libc-wrapper-forwarder";
        } else {
          int argReg = getRISCVPrintfFormatArgReg(target->getName());
          RISCVLibcFunctionDecode &decoded =
              getRISCVLibcFunctionDecodeCached(sec, *sourceFunc, decodeCache,
                                               perfStats);
          DenseMap<uint64_t, RISCVLibcRelocTarget> &relocTargets =
              getRISCVLibcRelocTargetsCached<ELFT>(sec, relocTargetCache,
                                                   perfStats);
          DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
              &controlFlowRelocs =
                  getRISCVLibcControlFlowRelocsCached<ELFT>(
                      sec, controlFlowRelocCache);
          if (proveRISCVLibcCallsiteFormat<ELFT>(
                  sec, decoded, rel.r_offset, argReg, relocTargets,
                  controlFlowRelocs, call.provenFormat, call.proof, call.reason,
                  call.entryCalleeSavedReason, call.entryCalleeSavedDetail,
                  call.localDominatingReason, call.localDominatingDetail,
                  call.loopCarriedReason, call.loopCarriedDetail)) {
            call.formatClass = RISCVLibcFormatClass::ProvenConstant;
          } else if (!call.candidateFormats.empty()) {
            call.formatClass = RISCVLibcFormatClass::CandidateConstant;
          } else {
            call.formatClass = RISCVLibcFormatClass::DynamicOrUnknown;
          }
        }
        printfCalls.push_back(std::move(call));
      }
    }
  };

  for (InputSectionBase *sec : ctx.inputSections) {
    if (!isRISCVLibcAuditSectionEligible(sec, mode))
      continue;
    RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
    recordRel(*sec, rels.rels);
    recordRel(*sec, rels.relas);
  }
}

template <class ELFT>
static RISCVLibcGlobalRouteAuditStats auditRISCVLibcGlobalRoutes(
    RISCVLibcAuditReachabilityMode mode,
    ArrayRef<RISCVLibcFunctionNode> nodes,
    ArrayRef<RISCVLibcPrintfCall> printfCalls, ArrayRef<unsigned> printfCoreRoots,
    std::map<std::pair<InputSectionBase *, Defined *>,
             RISCVLibcFunctionDecode> &decodeCache,
    RISCVLibcAuditPerfStats &perfStats, bool printRoutes,
    StringRef routePrefix) {
  RISCVLibcGlobalRouteAuditStats stats;
  stats.gateReady = printfCoreRoots.size() == 1;
  bool sawRelevantRoute = false;

  auto printGlobalRoute = [&](StringRef source, StringRef target,
                              RISCVLibcGlobalRouteKind kind, StringRef format,
                              bool safe) {
    if (!printRoutes)
      return;
    message(Twine("  ") + routePrefix + " source=" + source +
            " target=" + target +
            " kind=" + riscvLibcGlobalRouteKindToString(kind) +
            " format=" + format + " safe=" + Twine(safe ? 1 : 0));
  };

  for (const RISCVLibcPrintfCall &call : printfCalls) {
    sawRelevantRoute = true;
    if (call.formatClass == RISCVLibcFormatClass::InternalForwarder) {
      ++stats.internalForwarders;
      printGlobalRoute(call.caller->getName(), call.target->getName(),
                       RISCVLibcGlobalRouteKind::InternalForwarder,
                       "forwarded", true);
      continue;
    }

    ++stats.entryCalls;
    bool provenNonFloat =
        call.formatClass == RISCVLibcFormatClass::ProvenConstant &&
        !call.provenFormat.hasFloat && !call.provenFormat.hasLongDouble;
    bool provenFloat =
        call.formatClass == RISCVLibcFormatClass::ProvenConstant &&
        (call.provenFormat.hasFloat || call.provenFormat.hasLongDouble);
    if (provenNonFloat) {
      ++stats.provenNonFloatEntryCalls;
      printGlobalRoute(call.caller->getName(), call.target->getName(),
                       RISCVLibcGlobalRouteKind::DirectCall,
                       "proven-non-float", true);
    } else {
      stats.gateReady = false;
      if (provenFloat) {
        ++stats.floatEntryCalls;
        printGlobalRoute(call.caller->getName(), call.target->getName(),
                         RISCVLibcGlobalRouteKind::DirectCall,
                         call.provenFormat.hasLongDouble
                             ? StringRef("proven-long-double")
                             : StringRef("proven-float"),
                         false);
      } else {
        ++stats.unknownEntryCalls;
        printGlobalRoute(call.caller->getName(), call.target->getName(),
                         RISCVLibcGlobalRouteKind::DirectCall, "unknown",
                         false);
      }
    }
  }

  DenseSet<Defined *> printfCoreSyms;
  for (unsigned idx : printfCoreRoots)
    printfCoreSyms.insert(nodes[idx].sym);
  DenseSet<Defined *> printfFamilySyms;
  for (const RISCVLibcFunctionNode &node : nodes)
    if (isPrintfFamilyName(node.sym->getName()))
      printfFamilySyms.insert(node.sym);

  std::map<std::tuple<InputSectionBase *, Defined *, uint64_t, Defined *>,
           const RISCVLibcPrintfCall *>
      printfCallProofs;
  for (const RISCVLibcPrintfCall &call : printfCalls)
    printfCallProofs[{call.sourceSection, call.caller, call.callOffset,
                      call.target}] = &call;

  auto sameFunctionEntry = [](Defined *a, Defined *b) {
    if (!a || !b || a->type != STT_FUNC || b->type != STT_FUNC)
      return false;
    return a->section == b->section && a->value == b->value;
  };

  auto canonicalPrintfFamilyTarget = [&](Defined *target) -> Defined * {
    if (!target || target->type != STT_FUNC)
      return nullptr;
    if (isPrintfFamilyName(target->getName()))
      return target;
    for (Defined *entry : printfFamilySyms)
      if (sameFunctionEntry(target, entry))
        return entry;
    return nullptr;
  };

  auto canonicalPrintfCoreTarget = [&](Defined *target) -> Defined * {
    if (!target || target->type != STT_FUNC)
      return nullptr;
    for (Defined *core : printfCoreSyms)
      if (sameFunctionEntry(target, core))
        return core;
    return nullptr;
  };

  auto isRecognizedPrintfCoreInternalRoute = [&](Defined *source,
                                                Defined *target) {
    if (!source || !target)
      return false;
    if (!canonicalPrintfCoreTarget(target))
      return false;
    return llvm::any_of(printfCalls, [&](const RISCVLibcPrintfCall &call) {
      return call.formatClass == RISCVLibcFormatClass::InternalForwarder &&
             sameFunctionEntry(source, call.target);
    });
  };

  auto findProof = [&](InputSectionBase *sec, Defined *sourceFunc,
                       uint64_t offset, Defined *target) {
    auto it = printfCallProofs.find({sec, sourceFunc, offset, target});
    if (it != printfCallProofs.end())
      return it->second;
    for (const auto &entry : printfCallProofs)
      if (std::get<0>(entry.first) == sec &&
          std::get<1>(entry.first) == sourceFunc &&
          std::get<2>(entry.first) == offset &&
          sameFunctionEntry(std::get<3>(entry.first), target))
        return entry.second;
    return static_cast<const RISCVLibcPrintfCall *>(nullptr);
  };

  auto isDirectControlTransfer = [&](InputSectionBase &sec, Defined *sourceFunc,
                                     uint64_t offset, RelType type) {
    if (type == R_RISCV_CALL || type == R_RISCV_CALL_PLT)
      return true;
    if (type != R_RISCV_JAL && type != R_RISCV_RVC_JUMP)
      return false;
    if (!sourceFunc)
      return false;
    RISCVLibcFunctionDecode &decoded =
        getRISCVLibcFunctionDecodeCached(sec, *sourceFunc, decodeCache,
                                         perfStats);
    const RISCVLibcInsn *insn = getRISCVLibcInsnAt(decoded, offset);
    return insn && insn->controlFlow;
  };

  for (InputSectionBase *sec : ctx.inputSections) {
    if (!isRISCVLibcAuditSectionEligible(sec, mode))
      continue;
    RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
    auto scanGlobalRoutes = [&](auto rels) {
      for (const auto &rel : rels) {
        Symbol &targetSym = sec->getFile<ELFT>()->getRelocTargetSym(rel);
        StringRef targetName = targetSym.getName();
        Defined *target = dyn_cast<Defined>(&targetSym);
        bool nameIsPrintfFamily = isPrintfFamilyName(targetName);
        bool nameIsPrintfCore = targetName == "printf_core";
        if (!target) {
          if (!nameIsPrintfFamily && !nameIsPrintfCore)
            continue;
          sawRelevantRoute = true;
          ++stats.unresolvedRoutes;
          stats.gateReady = false;
          Defined *sourceFunc = nullptr;
          if (sec->flags & SHF_EXECINSTR)
            sourceFunc = sec->getEnclosingFunction(rel.r_offset);
          std::string sourceName =
              sourceFunc ? sourceFunc->getName().str() : sec->name.str();
          printGlobalRoute(sourceName, targetName,
                           RISCVLibcGlobalRouteKind::Unresolved,
                           "unresolved-symbol", false);
          continue;
        }
        Defined *printfFamilyTarget = canonicalPrintfFamilyTarget(target);
        Defined *printfCoreTarget = canonicalPrintfCoreTarget(target);
        bool targetIsPrintfFamily = printfFamilyTarget != nullptr;
        bool targetIsPrintfCore = printfCoreTarget != nullptr;
        if (!targetIsPrintfFamily && !targetIsPrintfCore)
          continue;
        if ((targetIsPrintfFamily && printfFamilyTarget != target) ||
            (targetIsPrintfCore && printfCoreTarget != target))
          ++stats.aliasRoutes;

        RelType type = rel.getType(config->isMips64EL);
        Defined *sourceFunc = nullptr;
        if (sec->flags & SHF_EXECINSTR)
          sourceFunc = sec->getEnclosingFunction(rel.r_offset);
        std::string sourceName =
            sourceFunc ? sourceFunc->getName().str() : sec->name.str();
        bool isDirectTransfer =
            isDirectControlTransfer(*sec, sourceFunc, rel.r_offset, type);
        bool isPotentialDirectTransfer =
            type == R_RISCV_CALL || type == R_RISCV_CALL_PLT ||
            type == R_RISCV_JAL || type == R_RISCV_RVC_JUMP;

        if (targetIsPrintfCore) {
          sawRelevantRoute = true;
          ++stats.directPrintfCoreRoutes;
          if (isDirectTransfer &&
              isRecognizedPrintfCoreInternalRoute(sourceFunc,
                                                  printfCoreTarget)) {
            printGlobalRoute(sourceName, printfCoreTarget->getName(),
                             RISCVLibcGlobalRouteKind::DirectPrintfCoreRoute,
                             "recognized-internal", true);
          } else {
            ++stats.unrecognizedPrintfCoreRoutes;
            stats.gateReady = false;
            printGlobalRoute(sourceName, printfCoreTarget->getName(),
                             isPotentialDirectTransfer
                                 ? RISCVLibcGlobalRouteKind::
                                       DirectPrintfCoreRoute
                                 : RISCVLibcGlobalRouteKind::NonCallReference,
                             isPotentialDirectTransfer
                                 ? StringRef("unrecognized")
                                 : StringRef("address-taken"),
                             false);
          }
          continue;
        }

        if (isPotentialDirectTransfer) {
          sawRelevantRoute = true;
          ++stats.directEntryRoutes;
          if (!isDirectTransfer) {
            ++stats.unresolvedRoutes;
            ++stats.missingProofRoutes;
            stats.gateReady = false;
            printGlobalRoute(sourceName, printfFamilyTarget->getName(),
                             RISCVLibcGlobalRouteKind::Unresolved,
                             "unresolved-control-transfer", false);
            continue;
          }
          const RISCVLibcPrintfCall *proof =
              findProof(sec, sourceFunc, rel.r_offset, printfFamilyTarget);
          if (!proof) {
            ++stats.missingProofRoutes;
            stats.gateReady = false;
            printGlobalRoute(sourceName, printfFamilyTarget->getName(),
                             RISCVLibcGlobalRouteKind::DirectCall,
                             "missing-proof-record", false);
          } else {
            ++stats.matchedProofRoutes;
          }
          continue;
        }

        if (!isDirectTransfer) {
          sawRelevantRoute = true;
          ++stats.nonCallRefs;
          ++stats.addressTakenRefs;
          stats.gateReady = false;
          printGlobalRoute(sourceName, printfFamilyTarget->getName(),
                           RISCVLibcGlobalRouteKind::NonCallReference,
                           "address-taken", false);
        }
      }
    };
    scanGlobalRoutes(rels.rels);
    scanGlobalRoutes(rels.relas);
  }

  if (!sawRelevantRoute) {
    ++stats.unresolvedRoutes;
    stats.gateReady = false;
  }
  return stats;
}

static bool isRISCVPrintfSpecializationCallPair(ArrayRef<uint8_t> content,
                                                uint64_t off) {
  if (off > content.size() || content.size() - off < 8)
    return false;
  uint32_t auipc = llvm::support::endian::read32le(content.data() + off);
  uint32_t jalr = llvm::support::endian::read32le(content.data() + off + 4);
  if ((auipc & 0x7f) != 0x17)
    return false;
  if ((jalr & 0x7f) != 0x67)
    return false;
  int rd = (auipc >> 7) & 0x1f;
  int jalrRd = (jalr >> 7) & 0x1f;
  int rs1 = (jalr >> 15) & 0x1f;
  int funct3 = (jalr >> 12) & 0x7;
  int imm = static_cast<int32_t>(jalr) >> 20;
  return rd == rs1 && isRISCVLibcLinkReg(jalrRd) && funct3 == 0 && imm == 0;
}

template <class ELFT>
static RISCVPrintfSpecializationStats
specializeRISCVPrintfCoreFloatCalls(InputSectionBase &sec, Defined &printfCore,
                                    RelsOrRelas<ELFT> rels) {
  RISCVPrintfSpecializationStats stats;
  if (sec.kind() != SectionBase::Regular) {
    stats.fallbackReason = "printf-core-not-regular-input-section";
    return stats;
  }
  if (sec.name != ".text.printf_core") {
    stats.fallbackReason = "printf-core-section-name-unsupported";
    return stats;
  }
  if (riscvRelocOverrideStorage.contains(&sec)) {
    stats.fallbackReason = "relocation-override-already-present";
    return stats;
  }
  if (rels.areRelocsRel()) {
    stats.fallbackReason = "rel-relocations-unsupported";
    return stats;
  }

  using Elf_Rela = typename ELFT::Rela;
  SmallVector<uint64_t, 0> callOffsets;
  DenseSet<uint64_t> callOffsetSet;
  DenseSet<uint64_t> removableRelocIndexes;
  ArrayRef<uint8_t> content = sec.content();
  uint64_t funcEnd = printfCore.value + printfCore.size;
  if (printfCore.value > content.size() || funcEnd > content.size()) {
    stats.fallbackReason = "printf-core-range-out-of-section";
    return stats;
  }

  for (auto [i, rel] : llvm::enumerate(rels.relas)) {
    RelType type = rel.getType(config->isMips64EL);
    if (type != R_RISCV_CALL && type != R_RISCV_CALL_PLT)
      continue;
    if (rel.r_offset < printfCore.value || rel.r_offset >= funcEnd)
      continue;
    Symbol &targetSym = sec.getFile<ELFT>()->getRelocTargetSym(rel);
    Defined *target = dyn_cast<Defined>(&targetSym);
    if (!target || !isRISCVPrintfCoreFloatHelperName(target->getName()))
      continue;
    if (!isRISCVPrintfSpecializationCallPair(content, rel.r_offset)) {
      stats.fallbackReason = "unexpected-call-encoding";
      return stats;
    }
    if (callOffsetSet.insert(rel.r_offset).second)
      callOffsets.push_back(rel.r_offset);
    removableRelocIndexes.insert(i);
  }

  if (callOffsets.empty()) {
    stats.fallbackReason = "no-float-helper-calls";
    return stats;
  }

  for (auto [i, rel] : llvm::enumerate(rels.relas)) {
    bool inCallPair = false;
    for (uint64_t off : callOffsets)
      if (rel.r_offset >= off && rel.r_offset < off + 8) {
        inCallPair = true;
        break;
      }
    if (!inCallPair)
      continue;
    RelType type = rel.getType(config->isMips64EL);
    if (callOffsetSet.contains(rel.r_offset) &&
        (type == R_RISCV_CALL || type == R_RISCV_CALL_PLT ||
         type == R_RISCV_RELAX)) {
      removableRelocIndexes.insert(i);
      continue;
    }
    stats.fallbackReason = "overlapping-relocation-at-call-offset";
    return stats;
  }

  uint8_t *newContent = makeThreadLocalN<uint8_t>(content.size());
  llvm::copy(content, newContent);
  for (uint64_t off : callOffsets) {
    llvm::support::endian::write32le(newContent + off, 0x00000013);
    llvm::support::endian::write32le(newContent + off + 4, 0x00000013);
  }

  SmallVector<Elf_Rela, 0> keptRelas;
  keptRelas.reserve(rels.relas.size() - removableRelocIndexes.size());
  for (auto [i, rel] : llvm::enumerate(rels.relas))
    if (!removableRelocIndexes.contains(i))
      keptRelas.push_back(rel);

  auto *kept = makeThreadLocalN<Elf_Rela>(keptRelas.size());
  llvm::copy(keptRelas, kept);
  RISCVRelocOverrideStorage storage;
  storage.relocsAreRela = true;
  storage.relocs = kept;
  storage.relocCount = static_cast<uint32_t>(keptRelas.size());
  riscvRelocOverrideStorage[&sec] = storage;

  sec.content_ = newContent;
  stats.applied = true;
  stats.floatCallsNopped = static_cast<uint32_t>(callOffsets.size());
  stats.callRelocsRemoved = stats.floatCallsNopped;
  stats.relaxRelocsRemoved =
      static_cast<uint32_t>(removableRelocIndexes.size() - callOffsets.size());
  return stats;
}

template <class ELFT>
static void runRISCVPrintfSpecializationPreGC() {
  if ((!config->printRISCVLibcSpecializationAudit &&
       !config->riscvPrintfSpecialization) ||
      config->emachine != EM_RISCV)
    return;

  RISCVLibcAuditPerfStats perfStats;
  std::map<std::pair<InputSectionBase *, Defined *>, RISCVLibcFunctionDecode>
      decodeCache;
  std::map<InputSectionBase *, DenseMap<uint64_t, RISCVLibcRelocTarget>>
      relocTargetCache;
  std::map<InputSectionBase *,
           DenseMap<uint64_t,
                    SmallVector<RISCVLibcControlFlowRelocInfo, 0>>>
      controlFlowRelocCache;

  SmallVector<RISCVLibcFunctionNode, 0> nodes;
  DenseMap<Defined *, unsigned> nodeIndex;
  SmallVector<RISCVLibcPrintfCall, 0> printfCalls;
  RISCVLibcPrintfCallCollectionStats callStats;
  collectRISCVLibcAuditGraph<ELFT>(
      RISCVLibcAuditReachabilityMode::PreGCConservative, nodes, nodeIndex,
      printfCalls, callStats, decodeCache, relocTargetCache,
      controlFlowRelocCache, perfStats);

  SmallVector<unsigned, 0> printfCoreRoots;
  for (auto [i, node] : llvm::enumerate(nodes))
    if (node.sym->getName() == "printf_core")
      printfCoreRoots.push_back(i);

  RISCVLibcGlobalRouteAuditStats gate =
      auditRISCVLibcGlobalRoutes<ELFT>(
          RISCVLibcAuditReachabilityMode::PreGCConservative, nodes,
          printfCalls, printfCoreRoots, decodeCache, perfStats, false,
          "printf_pre_gc_route");

  RISCVPrintfSpecializationStats transformStats;
  if (!config->riscvPrintfSpecialization) {
    transformStats.fallbackReason = "option-disabled";
  } else if (!gate.gateReady) {
    transformStats.fallbackReason = "pre-gc-gate-not-ready";
  } else if (printfCoreRoots.size() != 1) {
    transformStats.fallbackReason = "printf-core-not-unique";
  } else {
    RISCVLibcFunctionNode &node = nodes[printfCoreRoots[0]];
    RelsOrRelas<ELFT> rels = node.section->template relsOrRelas<ELFT>();
    transformStats =
        specializeRISCVPrintfCoreFloatCalls<ELFT>(*node.section, *node.sym,
                                                  rels);
  }

  if (config->printRISCVLibcSpecializationAudit ||
      config->riscvPrintfSpecialization) {
    message("RISCV libc printf pre-GC specialization audit:");
    message(Twine("  printf_pre_gc_entry_calls=") + Twine(gate.entryCalls));
    message(Twine("  printf_pre_gc_proven_non_float_entry_calls=") +
            Twine(gate.provenNonFloatEntryCalls));
    message(Twine("  printf_pre_gc_unknown_entry_calls=") +
            Twine(gate.unknownEntryCalls));
    message(Twine("  printf_pre_gc_internal_forwarders=") +
            Twine(gate.internalForwarders));
    message(Twine("  printf_pre_gc_noncall_refs=") + Twine(gate.nonCallRefs));
    message(Twine("  printf_pre_gc_address_taken_refs=") +
            Twine(gate.addressTakenRefs));
    message(Twine("  printf_pre_gc_direct_entry_routes=") +
            Twine(gate.directEntryRoutes));
    message(Twine("  printf_pre_gc_matched_proof_routes=") +
            Twine(gate.matchedProofRoutes));
    message(Twine("  printf_pre_gc_missing_proof_routes=") +
            Twine(gate.missingProofRoutes));
    message(Twine("  printf_pre_gc_direct_printf_core_routes=") +
            Twine(gate.directPrintfCoreRoutes));
    message(Twine("  printf_pre_gc_unrecognized_printf_core_routes=") +
            Twine(gate.unrecognizedPrintfCoreRoutes));
    message(Twine("  printf_pre_gc_unresolved_routes=") +
            Twine(gate.unresolvedRoutes));
    message(Twine("  printf_pre_gc_alias_routes=") + Twine(gate.aliasRoutes));
    message(Twine("  printf_pre_gc_specialization_gate_ready=") +
            Twine(gate.gateReady ? 1 : 0));
    message(Twine("  printf_specialization_applied=") +
            Twine(transformStats.applied ? 1 : 0));
    message(Twine("  printf_specialization_float_calls_nopped=") +
            Twine(transformStats.floatCallsNopped));
    message(Twine("  printf_specialization_call_relocs_removed=") +
            Twine(transformStats.callRelocsRemoved));
    message(Twine("  printf_specialization_relax_relocs_removed=") +
            Twine(transformStats.relaxRelocsRemoved));
    message(Twine("  printf_specialization_fallback_reason=") +
            transformStats.fallbackReason);
  }
}

template <class ELFT> static void printRISCVLibcSpecializationAudit() {
  if (!config->printRISCVLibcSpecializationAudit ||
      config->emachine != EM_RISCV)
    return;

  DenseSet<uint64_t> requestedCallOffsetDumpSet;
  if (!config->riscvLibcSpecializationAuditDumpCallOffsets.empty()) {
    SmallVector<StringRef, 0> pieces;
    config->riscvLibcSpecializationAuditDumpCallOffsets.split(pieces, ',',
                                                              -1, false);
    for (StringRef piece : pieces) {
      uint64_t value = 0;
      if (!piece.trim().getAsInteger(0, value))
        requestedCallOffsetDumpSet.insert(value);
    }
  }

  RISCVLibcAuditPerfStats perfStats;
  std::map<std::pair<InputSectionBase *, Defined *>, RISCVLibcFunctionDecode>
      decodeCache;
  std::map<InputSectionBase *, DenseMap<uint64_t, RISCVLibcRelocTarget>>
      relocTargetCache;
  std::map<InputSectionBase *,
           DenseMap<uint64_t,
                    SmallVector<RISCVLibcControlFlowRelocInfo, 0>>>
      controlFlowRelocCache;

  SmallVector<RISCVLibcFunctionNode, 0> nodes;
  DenseMap<Defined *, unsigned> nodeIndex;
  SmallVector<RISCVLibcPrintfCall, 0> printfCalls;
  RISCVLibcPrintfCallCollectionStats callStats;
  collectRISCVLibcAuditGraph<ELFT>(
      RISCVLibcAuditReachabilityMode::PostGCLiveOnly, nodes, nodeIndex,
      printfCalls, callStats, decodeCache, relocTargetCache,
      controlFlowRelocCache, perfStats);

  SmallVector<unsigned, 0> printfCoreRoots;
  for (auto [i, node] : llvm::enumerate(nodes))
    if (node.sym->getName() == "printf_core")
      printfCoreRoots.push_back(i);

  DenseSet<unsigned> closure;
  SmallVector<unsigned, 0> worklist;
  for (unsigned i : printfCoreRoots) {
    closure.insert(i);
    worklist.push_back(i);
  }
  while (!worklist.empty()) {
    unsigned i = worklist.pop_back_val();
    for (unsigned callee : nodes[i].callees)
      if (closure.insert(callee).second)
        worklist.push_back(callee);
  }

  auto isPrintfCoreRoot = [&](unsigned idx) {
    return llvm::is_contained(printfCoreRoots, idx);
  };
  auto outsideLiveIncoming = [&](unsigned idx) {
    uint32_t count = 0;
    for (const RISCVLibcIncomingRef &ref : nodes[idx].incoming) {
      if (!ref.sourceLive)
        continue;
      if (!ref.sourceFunction) {
        ++count;
        continue;
      }
      auto sourceIt = nodeIndex.find(ref.sourceFunction);
      if (sourceIt == nodeIndex.end() || !closure.contains(sourceIt->second))
        ++count;
    }
    return count;
  };

  uint64_t dependencyBytes = 0, exclusiveBytes = 0, sharedBytes = 0;
  uint32_t dependencyFunctions = 0, exclusiveFunctions = 0,
           sharedFunctions = 0;
  SmallVector<std::pair<uint64_t, unsigned>, 0> exclusiveBySize;
  for (unsigned idx : closure) {
    if (isPrintfCoreRoot(idx))
      continue;
    ++dependencyFunctions;
    dependencyBytes += nodes[idx].size;
    uint32_t outside = outsideLiveIncoming(idx);
    if (outside == 0) {
      ++exclusiveFunctions;
      exclusiveBytes += nodes[idx].size;
      exclusiveBySize.push_back({nodes[idx].size, idx});
    } else {
      ++sharedFunctions;
      sharedBytes += nodes[idx].size;
    }
  }
  llvm::sort(exclusiveBySize, [](const auto &a, const auto &b) {
    return a.first > b.first;
  });

  DenseSet<Defined *> printfCallers;
  uint32_t provenFormats = 0, candidateFormats = 0, unknownFormats = 0;
  uint32_t userPrintfCalls = 0, provenUserFormats = 0, candidateUserFormats = 0,
           unknownUserFormats = 0, internalForwarderCalls = 0;
  uint32_t provenFloatFormats = 0, provenLongDoubleFormats = 0;
  uint32_t provenDirectAbsFormatArgs = 0;
  uint32_t provenEntryCalleeSavedFormats = 0;
  uint32_t provenLocalDominatingCalleeSavedFormats = 0;
  uint32_t provenLoopCarriedCalleeSavedFormats = 0;
  uint32_t localDominatingAttempts = 0;
  uint32_t localDominatingFailFinalCopy = 0;
  uint32_t localDominatingFailInitNotFound = 0;
  uint32_t localDominatingFailIntermediateCall = 0;
  uint32_t localDominatingFailControlFlowBoundary = 0;
  uint32_t localDominatingFailFormatRegisterClobbered = 0;
  uint32_t localDominatingFailNearestDef = 0;
  uint32_t localDominatingFailTargetNotString = 0;
  uint32_t localDominatingFailClobbered = 0;
  uint32_t localDominatingFailExternalEntry = 0;
  uint32_t localDominatingFailUnknownControlFlow = 0;
  uint32_t localDominatingFailUnsupported = 0;
  uint32_t localDominatingFailOther = 0;
  uint32_t loopCarriedAttempts = 0;
  uint32_t loopCarriedFailExternalEntry = 0;
  uint32_t loopCarriedFailClobbered = 0;
  uint32_t loopCarriedFailUnknownControlFlow = 0;
  uint32_t loopCarriedFailOther = 0;
  uint32_t stackSlotFailedCalls = 0;
  uint32_t stackSlotLoadsRecognized = 0;
  uint32_t stackSlotNearestStoreFound = 0;
  uint32_t stackSlotNearestStoreIsCSWSP = 0;
  uint32_t stackSlotNearestStoreSrcCopy = 0;
  uint32_t stackSlotNearestStoreCopyFromCalleeSaved = 0;
  uint32_t stackSlotNearestStoreConstFormatProven = 0;
  uint32_t stackSlotNearestStoreNotProven = 0;
  uint32_t stackSlotCFGCandidates = 0;
  uint32_t stackSlotStoreDominatesLoad = 0;
  uint32_t stackSlotNoSameSlotClobber = 0;
  uint32_t stackSlotSPStable = 0;
  uint32_t stackSlotNoExternalEntry = 0;
  uint32_t stackSlotNoUnknownControlFlow = 0;
  uint32_t stackSlotCFGSafe = 0;
  DenseSet<int64_t> stackSlotUniqueOffsets;
  bool candidateFloatFormatSeen = false, candidateLongDoubleFormatSeen = false;
  for (RISCVLibcPrintfCall &call : printfCalls) {
    printfCallers.insert(call.caller);
    if (call.formatClass == RISCVLibcFormatClass::InternalForwarder) {
      ++internalForwarderCalls;
      continue;
    }
    ++userPrintfCalls;
    if (!call.localDominatingReason.empty())
      ++localDominatingAttempts;
    if (!call.loopCarriedReason.empty())
      ++loopCarriedAttempts;
    if (!call.loopCarriedReason.empty() &&
        call.loopCarriedReason != "accepted") {
      if (call.loopCarriedReason == "loop-carried-external-entry")
        ++loopCarriedFailExternalEntry;
      else if (call.loopCarriedReason ==
               "loop-carried-callee-saved-clobbered")
        ++loopCarriedFailClobbered;
      else if (call.loopCarriedReason == "loop-carried-unknown-control-flow")
        ++loopCarriedFailUnknownControlFlow;
      else
        ++loopCarriedFailOther;
    }
    if (!call.localDominatingReason.empty() &&
        call.localDominatingReason != "accepted") {
      if (call.localDominatingReason ==
          "local-callee-saved-final-copy-not-found")
        ++localDominatingFailFinalCopy;
      else if (call.localDominatingReason ==
               "local-callee-saved-init-not-found")
        ++localDominatingFailInitNotFound;
      else if (call.localDominatingReason == "intermediate-call")
        ++localDominatingFailIntermediateCall;
      else if (call.localDominatingReason == "control-flow-boundary")
        ++localDominatingFailControlFlowBoundary;
      else if (call.localDominatingReason == "format-register-clobbered")
        ++localDominatingFailFormatRegisterClobbered;
      else if (call.localDominatingReason ==
               "local-callee-saved-nearest-def-not-constant")
        ++localDominatingFailNearestDef;
      else if (call.localDominatingReason ==
               "local-callee-saved-target-not-string")
        ++localDominatingFailTargetNotString;
      else if (call.localDominatingReason ==
               "local-callee-saved-clobbered")
        ++localDominatingFailClobbered;
      else if (call.localDominatingReason ==
               "local-callee-saved-external-entry")
        ++localDominatingFailExternalEntry;
      else if (call.localDominatingReason ==
               "local-callee-saved-unknown-control-flow")
        ++localDominatingFailUnknownControlFlow;
      else if (call.localDominatingReason == "unsupported-instruction")
        ++localDominatingFailUnsupported;
      else
        ++localDominatingFailOther;
    }
    if (call.formatClass == RISCVLibcFormatClass::ProvenConstant) {
      ++provenFormats;
      ++provenUserFormats;
      if (call.provenFormat.hasFloat)
        ++provenFloatFormats;
      if (call.provenFormat.hasLongDouble)
        ++provenLongDoubleFormats;
      if (call.proof == "DIRECT_ABS_FORMAT_ARG")
        ++provenDirectAbsFormatArgs;
      if (StringRef(call.proof).startswith("ENTRY_CONST_CALLEE_SAVED_COPY"))
        ++provenEntryCalleeSavedFormats;
      if (StringRef(call.proof).startswith(
              "LOCAL_DOMINATING_CALLEE_SAVED_CONST"))
        ++provenLocalDominatingCalleeSavedFormats;
      if (StringRef(call.proof).startswith(
              "LOOP_CARRIED_CALLEE_SAVED_CONST"))
        ++provenLoopCarriedCalleeSavedFormats;
    } else if (call.formatClass == RISCVLibcFormatClass::CandidateConstant) {
      ++candidateFormats;
      ++candidateUserFormats;
      for (const RISCVLibcCandidateFormat &f : call.candidateFormats) {
        candidateFloatFormatSeen |= f.hasFloat;
        candidateLongDoubleFormatSeen |= f.hasLongDouble;
      }
    } else {
      ++unknownFormats;
      ++unknownUserFormats;
      for (const RISCVLibcCandidateFormat &f : call.candidateFormats) {
        candidateFloatFormatSeen |= f.hasFloat;
        candidateLongDoubleFormatSeen |= f.hasLongDouble;
      }
    }
  }
  bool allUserPrintfFormatsProvenNonFloat =
      userPrintfCalls > 0 && provenUserFormats == userPrintfCalls &&
      unknownUserFormats == 0 && provenFloatFormats == 0 &&
      provenLongDoubleFormats == 0;
  RISCVLibcGlobalRouteAuditStats globalStats =
      auditRISCVLibcGlobalRoutes<ELFT>(
          RISCVLibcAuditReachabilityMode::PostGCLiveOnly, nodes, printfCalls,
          printfCoreRoots, decodeCache, perfStats, true,
          "printf_global_route");

  SmallVector<RISCVLibcPrintfCoreFloatCall, 0> printfCoreFloatCalls;
  DenseSet<Defined *> printfCoreFloatHelpers;
  SmallVector<RISCVLibcPrintfCoreFloatRegion, 0> printfCoreFloatRegions;
  uint64_t printfCoreFloatCandidateBytes = 0;
  uint32_t printfCoreFloatInternalEdges = 0;
  uint32_t printfCoreFloatIncomingEdges = 0;
  uint32_t printfCoreFloatOutgoingEdges = 0;
  uint32_t printfCoreFloatIncomingFallthroughEdges = 0;
  uint32_t printfCoreFloatOutgoingFallthroughEdges = 0;
  uint32_t printfCoreFloatDispatchCandidates = 0;
  uint32_t printfCoreFloatUnknownControlFlow = 0;
  uint32_t printfCoreFloatHelperCallMisses = 0;
  bool printfCoreFloatRegionIsolatable = false;

  auto regionIndexFor = [&](InputSectionBase *section, Defined *function,
                            uint64_t off) -> int {
    for (auto [i, r] : llvm::enumerate(printfCoreFloatRegions))
      if (r.section == section && r.function == function &&
          containsRISCVLibcOffset(r, off))
        return static_cast<int>(i);
    return -1;
  };

  for (unsigned idx : printfCoreRoots) {
    RISCVLibcFunctionNode &node = nodes[idx];
    RISCVLibcFunctionDecode &decoded = getRISCVLibcFunctionDecodeCached(
        *node.section, *node.sym, decodeCache, perfStats);
    DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
        &controlFlowRelocs =
            getRISCVLibcControlFlowRelocsCached<ELFT>(*node.section,
                                                      controlFlowRelocCache);
    size_t firstCall = printfCoreFloatCalls.size();
    RelsOrRelas<ELFT> rels = node.section->template relsOrRelas<ELFT>();
    auto scanCallRels = [&](auto rels) {
      for (const auto &rel : rels) {
        if (rel.r_offset < node.sym->value ||
            rel.r_offset >= node.sym->value + node.sym->size)
          continue;
        RelType type = rel.getType(config->isMips64EL);
        if (type != R_RISCV_CALL && type != R_RISCV_CALL_PLT)
          continue;
        Symbol &targetSym =
            node.section->getFile<ELFT>()->getRelocTargetSym(rel);
        Defined *target = dyn_cast<Defined>(&targetSym);
        if (!target || !isRISCVPrintfCoreFloatHelperName(target->getName()))
          continue;
        RISCVLibcPrintfCoreFloatCall call;
        call.sourceSection = node.section;
        call.sourceFunction = node.sym;
        call.helper = target;
        call.targetSection = dyn_cast_or_null<InputSectionBase>(target->section);
        call.helperSize = target->size;
        call.relocOffset = rel.r_offset;
        call.callInsnOffset = getRISCVLibcCallInsnOffset(decoded, rel.r_offset);
        call.relocType = type;
        printfCoreFloatCalls.push_back(call);
        printfCoreFloatHelpers.insert(target);
      }
    };
    scanCallRels(rels.rels);
    scanCallRels(rels.relas);

    DenseSet<uint64_t> blockBoundaries;
    blockBoundaries.insert(decoded.funcStart);
    for (const RISCVLibcInsn &insn : decoded.instructions) {
      if (insn.offset < node.sym->value ||
          insn.offset >= node.sym->value + node.sym->size)
        continue;
      if (!isRISCVLibcNonCallControlFlow(controlFlowRelocs, insn))
        continue;
      if (const RISCVLibcInsn *next = getRISCVLibcNextInsn(decoded, insn))
        if (next->offset < node.sym->value + node.sym->size)
          blockBoundaries.insert(next->offset);
    }
    for (const auto &entry : controlFlowRelocs) {
      uint64_t source = entry.first;
      const RISCVLibcInsn *sourceInsn = getRISCVLibcInsnAt(decoded, source);
      if (!sourceInsn || source < node.sym->value ||
          source >= node.sym->value + node.sym->size)
        continue;
      for (const RISCVLibcControlFlowRelocInfo &r : entry.second) {
        if (!isRISCVLibcDirectBranchOrJumpReloc(r.type))
          continue;
        if (isRISCVLibcNormalDirectCall(controlFlowRelocs, *sourceInsn))
          continue;
        if (!r.hasTarget || r.targetSection != node.section)
          continue;
        if (r.targetOffset >= node.sym->value &&
            r.targetOffset < node.sym->value + node.sym->size &&
            getRISCVLibcInsnAt(decoded, r.targetOffset))
          blockBoundaries.insert(r.targetOffset);
      }
    }

    SmallVector<uint64_t, 0> sortedBoundaries;
    for (uint64_t off : blockBoundaries)
      sortedBoundaries.push_back(off);
    llvm::sort(sortedBoundaries);

    auto blockForCall = [&](uint64_t callOff,
                            RISCVLibcPrintfCoreFloatRegion &region) {
      if (!getRISCVLibcInsnAt(decoded, callOff))
        return false;
      auto it = llvm::upper_bound(sortedBoundaries, callOff);
      if (it == sortedBoundaries.begin())
        return false;
      uint64_t blockStart = *(it - 1);
      const RISCVLibcInsn *startInsn = getRISCVLibcInsnAt(decoded, blockStart);
      if (!startInsn)
        return false;
      uint64_t nextBoundary =
          it == sortedBoundaries.end() ? node.sym->value + node.sym->size : *it;
      uint64_t blockEnd = std::numeric_limits<uint64_t>::max();
      bool sawCall = false;
      for (const RISCVLibcInsn &insn : decoded.instructions) {
        if (insn.offset < blockStart)
          continue;
        if (insn.offset >= nextBoundary)
          break;
        if (insn.offset == callOff)
          sawCall = true;
        blockEnd = insn.offset + insn.size - 1;
        if (isRISCVLibcNonCallControlFlow(controlFlowRelocs, insn))
          break;
      }
      if (blockEnd == std::numeric_limits<uint64_t>::max() ||
          blockStart < node.sym->value ||
          blockEnd >= node.sym->value + node.sym->size || !sawCall ||
          callOff < blockStart || callOff > blockEnd)
        return false;
      region.section = node.section;
      region.function = node.sym;
      region.start = blockStart;
      region.end = blockEnd;
      region.helperCallCount = 1;
      return true;
    };

    for (const RISCVLibcPrintfCoreFloatCall &call :
         ArrayRef<RISCVLibcPrintfCoreFloatCall>(printfCoreFloatCalls)
             .slice(firstCall)) {
      if (call.callInsnOffset < node.sym->value ||
          call.callInsnOffset >= node.sym->value + node.sym->size)
        continue;
      RISCVLibcPrintfCoreFloatRegion r;
      if (!blockForCall(call.callInsnOffset, r)) {
        ++printfCoreFloatUnknownControlFlow;
        continue;
      }
      bool found = false;
      for (RISCVLibcPrintfCoreFloatRegion &old : printfCoreFloatRegions) {
        if (old.section == r.section && old.function == r.function &&
            old.start == r.start && old.end == r.end) {
          ++old.helperCallCount;
          found = true;
          break;
        }
      }
      if (!found)
        printfCoreFloatRegions.push_back(r);
    }

    llvm::sort(printfCoreFloatRegions,
               [](const RISCVLibcPrintfCoreFloatRegion &a,
                  const RISCVLibcPrintfCoreFloatRegion &b) {
                 if (a.section != b.section)
                   return a.section < b.section;
                 if (a.function != b.function)
                   return a.function < b.function;
                 return a.start < b.start;
               });
    for (const auto &entry : controlFlowRelocs) {
      uint64_t source = entry.first;
      for (const RISCVLibcControlFlowRelocInfo &r : entry.second) {
        if (!isRISCVLibcControlFlowAuditReloc(r.type))
          continue;
        int sourceRegion = regionIndexFor(node.section, node.sym, source);
        if (!r.hasTarget || r.targetSection != node.section) {
          if (sourceRegion >= 0)
            ++printfCoreFloatUnknownControlFlow;
          continue;
        }
        int targetRegion =
            regionIndexFor(node.section, node.sym, r.targetOffset);
        if (sourceRegion >= 0 && targetRegion >= 0 &&
            sourceRegion == targetRegion) {
          ++printfCoreFloatInternalEdges;
        } else if (sourceRegion < 0 && targetRegion >= 0) {
          ++printfCoreFloatIncomingEdges;
          ++printfCoreFloatDispatchCandidates;
          message(Twine("  float_dispatch_candidate source_offset=") +
                  hexOffset(source) + " target_offset=" +
                  hexOffset(r.targetOffset) + " relocation=" +
                  lld::toString(r.type) + " target_region=" +
                  Twine(targetRegion));
        } else if (sourceRegion >= 0 && targetRegion < 0) {
          ++printfCoreFloatOutgoingEdges;
        }
      }
    }

    for (const RISCVLibcPrintfCoreFloatRegion &region :
         printfCoreFloatRegions) {
      if (region.section != node.section || region.function != node.sym)
        continue;
      const RISCVLibcInsn *firstInsn = getRISCVLibcInsnAt(decoded, region.start);
      const RISCVLibcInsn *lastInsn = nullptr;
      for (const RISCVLibcInsn &insn : decoded.instructions) {
        if (insn.offset > region.end)
          break;
        if (insn.offset >= region.start)
          lastInsn = &insn;
      }
      if (!firstInsn || !lastInsn) {
        ++printfCoreFloatUnknownControlFlow;
        continue;
      }
      const RISCVLibcInsn *prevInsn = nullptr;
      for (const RISCVLibcInsn &insn : decoded.instructions) {
        if (insn.offset + insn.size == region.start) {
          prevInsn = &insn;
          break;
        }
      }
      if (prevInsn) {
        std::optional<bool> fallthrough =
            hasRISCVLibcKnownFallthrough(controlFlowRelocs, *prevInsn);
        if (!fallthrough) {
          ++printfCoreFloatUnknownControlFlow;
        } else if (*fallthrough) {
          ++printfCoreFloatIncomingFallthroughEdges;
          message(Twine("  float_region_edge kind=fallthrough direction=incoming"
                        " source_offset=") +
                  hexOffset(prevInsn->offset) + " target_offset=" +
                  hexOffset(region.start));
        }
      }
      std::optional<bool> fallthrough =
          hasRISCVLibcKnownFallthrough(controlFlowRelocs, *lastInsn);
      if (!fallthrough) {
        ++printfCoreFloatUnknownControlFlow;
      } else if (*fallthrough) {
        const RISCVLibcInsn *nextInsn = getRISCVLibcNextInsn(decoded, *lastInsn);
        if (nextInsn && !containsRISCVLibcOffset(region, nextInsn->offset)) {
          ++printfCoreFloatOutgoingFallthroughEdges;
          message(Twine("  float_region_edge kind=fallthrough direction=outgoing"
                        " source_offset=") +
                  hexOffset(lastInsn->offset) + " target_offset=" +
                  hexOffset(nextInsn->offset));
        }
      }
    }
  }

  for (const RISCVLibcPrintfCoreFloatCall &call : printfCoreFloatCalls) {
    uint32_t matches = 0;
    for (const RISCVLibcPrintfCoreFloatRegion &r : printfCoreFloatRegions)
      if (r.section == call.sourceSection && r.function == call.sourceFunction &&
          containsRISCVLibcOffset(r, call.callInsnOffset))
        ++matches;
    if (matches != 1) {
      ++printfCoreFloatHelperCallMisses;
      ++printfCoreFloatUnknownControlFlow;
    }
  }

  for (const RISCVLibcPrintfCoreFloatRegion &r : printfCoreFloatRegions)
    if (r.end >= r.start)
      printfCoreFloatCandidateBytes += r.end - r.start + 1;

  uint32_t failedCallsiteDumpRequested =
      config->riscvLibcSpecializationAuditDumpFailedCalls;
  uint32_t failedCallsiteDumpEmitted = 0;
  uint32_t requestedCallOffsetDumps = requestedCallOffsetDumpSet.size();
  uint32_t matchedCallOffsetDumps = 0;

  message("RISCV libc specialization audit:");
  message(Twine("  printf_core_instances=") + Twine(printfCoreRoots.size()));
  for (unsigned idx : printfCoreRoots) {
    const RISCVLibcFunctionNode &node = nodes[idx];
    message(Twine("  printf_core file=") + symbolFileName(*node.sym) +
            " section=" + node.section->name + " size=" + Twine(node.size));
    for (unsigned callee : node.callees) {
      const RISCVLibcFunctionNode &dst = nodes[callee];
      RISCVLibcRefKind kind = RISCVLibcRefKind::Unknown;
      for (const RISCVLibcIncomingRef &ref : dst.incoming)
        if (ref.sourceFunction == node.sym) {
          kind = ref.kind;
          break;
        }
      message(Twine("    printf_core -> ") + dst.sym->getName() +
              " size=" + Twine(dst.size) +
              " kind=" + riscvLibcRefKindToString(kind));
    }
  }

  message(Twine("  printf_dependency_functions=") +
          Twine(dependencyFunctions));
  message(Twine("  printf_dependency_bytes=") + Twine(dependencyBytes));
  message(Twine("  printf_exclusive_dependency_functions=") +
          Twine(exclusiveFunctions));
  message(Twine("  printf_exclusive_dependency_bytes=") +
          Twine(exclusiveBytes));
  message(Twine("  printf_shared_dependency_functions=") +
          Twine(sharedFunctions));
  message(Twine("  printf_shared_dependency_bytes=") + Twine(sharedBytes));

  uint32_t printed = 0;
  for (auto [size, idx] : exclusiveBySize) {
    if (printed++ == 15)
      break;
    const RISCVLibcFunctionNode &node = nodes[idx];
    message(Twine("  exclusive function=") + node.sym->getName() +
            " size=" + Twine(size) + " outside_live_incoming=0 file=" +
            symbolFileName(*node.sym) + " section=" + node.section->name);
  }

  for (auto [i, node] : llvm::enumerate(nodes)) {
    if (!isPrintfFloatDependencyName(node.sym->getName()))
      continue;
    bool inClosure = closure.contains(i);
    bool exclusive = inClosure && !isPrintfCoreRoot(i) &&
                     outsideLiveIncoming(i) == 0;
    message(Twine("  float_dependency_probe function=") + node.sym->getName() +
            " size=" + Twine(node.size) +
            " in_printf_closure=" + Twine(inClosure ? 1 : 0) +
            " exclusive=" + Twine(exclusive ? 1 : 0) +
            " outside_live_incoming=" + Twine(outsideLiveIncoming(i)));
  }

  for (const RISCVLibcPrintfCoreFloatCall &call : printfCoreFloatCalls) {
    message(Twine("  printf_core_float_call helper=") +
            call.helper->getName() + " call_offset=" +
            hexOffset(call.relocOffset) + " call_insn_offset=" +
            hexOffset(call.callInsnOffset) + " reloc=" +
            lld::toString(call.relocType) + " target_section=" +
            (call.targetSection ? call.targetSection->name
                                : StringRef("none")) +
            " target_size=" + Twine(call.helperSize));
  }
  for (auto [i, region] : llvm::enumerate(printfCoreFloatRegions))
    message(Twine("  printf_core_float_region index=") + Twine(i) +
            " start=" + hexOffset(region.start) +
            " end=" + hexOffset(region.end) + " bytes=" +
            Twine(region.end >= region.start ? region.end - region.start + 1
                                             : 0) +
            " helper_calls=" + Twine(region.helperCallCount));

  for (RISCVLibcPrintfCall &call : printfCalls) {
    bool dumpByOffset =
        call.formatClass != RISCVLibcFormatClass::InternalForwarder &&
        requestedCallOffsetDumpSet.contains(call.callOffset);
    if (dumpByOffset)
      ++matchedCallOffsetDumps;
    bool shouldDumpFailedContext =
        call.formatClass != RISCVLibcFormatClass::ProvenConstant &&
        call.formatClass != RISCVLibcFormatClass::InternalForwarder &&
        failedCallsiteDumpEmitted < failedCallsiteDumpRequested;
    bool shouldDumpContext = shouldDumpFailedContext || dumpByOffset;
    message(Twine("  printf_call caller=") + call.caller->getName() +
            " target=" + call.target->getName() +
            " source_section=" + call.sourceSection->name +
            " call_offset=" + hexOffset(call.callOffset) +
            " reloc=" + lld::toString(call.type) + " source_live=1" +
            " format_class=" + riscvLibcFormatClassToString(call.formatClass));
    if (call.formatClass == RISCVLibcFormatClass::ProvenConstant) {
      message(Twine("    format=\"") + call.provenFormat.text +
              "\" float=" + Twine(call.provenFormat.hasFloat ? 1 : 0) +
              " long_double=" +
              Twine(call.provenFormat.hasLongDouble ? 1 : 0) +
              " proof=" + call.proof);
    } else if (call.formatClass == RISCVLibcFormatClass::CandidateConstant) {
      for (const RISCVLibcCandidateFormat &f : call.candidateFormats)
        message(Twine("    candidate_format=\"") + f.text +
                "\" float=" + Twine(f.hasFloat ? 1 : 0) +
                " long_double=" + Twine(f.hasLongDouble ? 1 : 0));
      if (!call.reason.empty())
        message(Twine("    reason=") + call.reason);
    } else if (!call.reason.empty()) {
      message(Twine("    reason=") + call.reason);
    }
    if (!call.entryCalleeSavedReason.empty())
      message(Twine("    entry_callee_saved_reason=") +
              call.entryCalleeSavedReason);
    if (!call.entryCalleeSavedDetail.empty())
      message(Twine("    ") + call.entryCalleeSavedDetail);
    if (!call.localDominatingReason.empty())
      message(Twine("    local_dominating_reason=") +
              call.localDominatingReason);
    if (!call.localDominatingDetail.empty())
      message(Twine("    ") + call.localDominatingDetail);
    if (!call.loopCarriedReason.empty())
      message(Twine("    loop_reason=") + call.loopCarriedReason);
    if (!call.loopCarriedDetail.empty())
      message(Twine("    ") + call.loopCarriedDetail);
    if (shouldDumpContext) {
      RISCVLibcFunctionDecode &decoded = getRISCVLibcFunctionDecodeCached(
          *call.sourceSection, *call.caller, decodeCache, perfStats);
      dumpRISCVLibcFailedCallsiteContext<ELFT>(call, decoded);
      if (shouldDumpFailedContext)
        ++failedCallsiteDumpEmitted;
    }
    if (call.formatClass == RISCVLibcFormatClass::CandidateConstant) {
      ++stackSlotFailedCalls;
      RISCVLibcFunctionDecode &decoded = getRISCVLibcFunctionDecodeCached(
          *call.sourceSection, *call.caller, decodeCache, perfStats);
      DenseMap<uint64_t, SmallVector<RISCVLibcControlFlowRelocInfo, 0>>
          &controlFlowRelocs = getRISCVLibcControlFlowRelocsCached<ELFT>(
              *call.sourceSection, controlFlowRelocCache);
      dumpRISCVLibcStackSlotAudit<ELFT>(
          call, decoded, controlFlowRelocs, stackSlotLoadsRecognized,
          stackSlotUniqueOffsets, stackSlotNearestStoreFound,
          stackSlotNearestStoreIsCSWSP, stackSlotNearestStoreSrcCopy,
          stackSlotNearestStoreCopyFromCalleeSaved,
          stackSlotNearestStoreConstFormatProven,
          stackSlotNearestStoreNotProven, stackSlotCFGCandidates,
          stackSlotStoreDominatesLoad, stackSlotNoSameSlotClobber,
          stackSlotSPStable, stackSlotNoExternalEntry,
          stackSlotNoUnknownControlFlow, stackSlotCFGSafe);
    }
  }

  message(Twine("  printf_family_live_calls=") + Twine(printfCalls.size()));
  message(Twine("  printf_direct_call_records_raw=") +
          Twine(callStats.rawPrintfDirectCallRecords));
  message(Twine("  printf_unique_direct_callsites=") +
          Twine(printfCalls.size()));
  message(Twine("  printf_duplicate_direct_call_records=") +
          Twine(callStats.duplicatePrintfDirectCallRecords));
  message(Twine("  printf_family_callers=") + Twine(printfCallers.size()));
  message(Twine("  proven_constant_format_calls=") + Twine(provenFormats));
  message(Twine("  candidate_constant_format_calls=") +
          Twine(candidateFormats));
  message(Twine("  dynamic_or_unknown_format_calls=") + Twine(unknownFormats));
  message(Twine("  user_printf_family_calls=") + Twine(userPrintfCalls));
  message(Twine("  proven_user_printf_formats=") + Twine(provenUserFormats));
  message(Twine("  candidate_user_printf_formats=") +
          Twine(candidateUserFormats));
  message(Twine("  unknown_user_printf_formats=") + Twine(unknownUserFormats));
  message(Twine("  printf_internal_forwarder_calls=") +
          Twine(internalForwarderCalls));
  message(Twine("  proven_float_format_calls=") +
          Twine(provenFloatFormats));
  message(Twine("  proven_long_double_format_calls=") +
          Twine(provenLongDoubleFormats));
  message(Twine("  proven_direct_abs_format_args=") +
          Twine(provenDirectAbsFormatArgs));
  message(Twine("  proven_entry_callee_saved_formats=") +
          Twine(provenEntryCalleeSavedFormats));
  message(Twine("  proven_local_dominating_callee_saved_formats=") +
          Twine(provenLocalDominatingCalleeSavedFormats));
  message(Twine("  proven_loop_carried_callee_saved_formats=") +
          Twine(provenLoopCarriedCalleeSavedFormats));
  message(Twine("  local_dominating_attempts=") +
          Twine(localDominatingAttempts));
  message(Twine("  local_dominating_successes=") +
          Twine(provenLocalDominatingCalleeSavedFormats));
  message(Twine("  local_dominating_fail_final_copy=") +
          Twine(localDominatingFailFinalCopy));
  message(Twine("  local_dominating_fail_init_not_found=") +
          Twine(localDominatingFailInitNotFound));
  message(Twine("  local_dominating_fail_intermediate_call=") +
          Twine(localDominatingFailIntermediateCall));
  message(Twine("  local_dominating_fail_control_flow_boundary=") +
          Twine(localDominatingFailControlFlowBoundary));
  message(Twine("  local_dominating_fail_format_register_clobbered=") +
          Twine(localDominatingFailFormatRegisterClobbered));
  message(Twine("  local_dominating_fail_nearest_def=") +
          Twine(localDominatingFailNearestDef));
  message(Twine("  local_dominating_fail_target_not_string=") +
          Twine(localDominatingFailTargetNotString));
  message(Twine("  local_dominating_fail_clobbered=") +
          Twine(localDominatingFailClobbered));
  message(Twine("  local_dominating_fail_external_entry=") +
          Twine(localDominatingFailExternalEntry));
  message(Twine("  local_dominating_fail_unknown_control_flow=") +
          Twine(localDominatingFailUnknownControlFlow));
  message(Twine("  local_dominating_fail_unsupported=") +
          Twine(localDominatingFailUnsupported));
  message(Twine("  local_dominating_fail_other=") +
          Twine(localDominatingFailOther));
  message(Twine("  loop_carried_attempts=") +
          Twine(loopCarriedAttempts));
  message(Twine("  loop_carried_successes=") +
          Twine(provenLoopCarriedCalleeSavedFormats));
  message(Twine("  loop_carried_fail_external_entry=") +
          Twine(loopCarriedFailExternalEntry));
  message(Twine("  loop_carried_fail_clobbered=") +
          Twine(loopCarriedFailClobbered));
  message(Twine("  loop_carried_fail_unknown_control_flow=") +
          Twine(loopCarriedFailUnknownControlFlow));
  message(Twine("  loop_carried_fail_other=") +
          Twine(loopCarriedFailOther));
  message(Twine("  printf_stack_slot_failed_calls=") +
          Twine(stackSlotFailedCalls));
  message(Twine("  printf_stack_slot_loads_recognized=") +
          Twine(stackSlotLoadsRecognized));
  message(Twine("  printf_stack_slot_unique_offsets=") +
          Twine(stackSlotUniqueOffsets.size()));
  message(Twine("  printf_stack_slot_nearest_store_found=") +
          Twine(stackSlotNearestStoreFound));
  message(Twine("  printf_stack_slot_nearest_store_is_cswsp=") +
          Twine(stackSlotNearestStoreIsCSWSP));
  message(Twine("  printf_stack_slot_nearest_store_src_copy=") +
          Twine(stackSlotNearestStoreSrcCopy));
  message(Twine("  printf_stack_slot_nearest_store_copy_from_callee_saved=") +
          Twine(stackSlotNearestStoreCopyFromCalleeSaved));
  message(Twine("  printf_stack_slot_nearest_store_const_format_proven=") +
          Twine(stackSlotNearestStoreConstFormatProven));
  message(Twine("  printf_stack_slot_nearest_store_not_proven=") +
          Twine(stackSlotNearestStoreNotProven));
  message(Twine("  printf_stack_slot_cfg_candidates=") +
          Twine(stackSlotCFGCandidates));
  message(Twine("  printf_stack_slot_store_dominates_load=") +
          Twine(stackSlotStoreDominatesLoad));
  message(Twine("  printf_stack_slot_no_same_slot_clobber=") +
          Twine(stackSlotNoSameSlotClobber));
  message(Twine("  printf_stack_slot_sp_stable=") +
          Twine(stackSlotSPStable));
  message(Twine("  printf_stack_slot_no_external_entry=") +
          Twine(stackSlotNoExternalEntry));
  message(Twine("  printf_stack_slot_no_unknown_control_flow=") +
          Twine(stackSlotNoUnknownControlFlow));
  message(Twine("  printf_stack_slot_cfg_safe=") + Twine(stackSlotCFGSafe));
  message(Twine("  all_user_printf_formats_proven_non_float=") +
          Twine(allUserPrintfFormatsProvenNonFloat ? 1 : 0));
  message(Twine("  printf_specialization_gate_ready=") +
          Twine(allUserPrintfFormatsProvenNonFloat ? 1 : 0));
  message(Twine("  printf_global_live_entry_calls=") +
          Twine(globalStats.entryCalls));
  message(Twine("  printf_global_proven_non_float_entry_calls=") +
          Twine(globalStats.provenNonFloatEntryCalls));
  message(Twine("  printf_global_float_entry_calls=") +
          Twine(globalStats.floatEntryCalls));
  message(Twine("  printf_global_unknown_entry_calls=") +
          Twine(globalStats.unknownEntryCalls));
  message(Twine("  printf_global_internal_forwarders=") +
          Twine(globalStats.internalForwarders));
  message(Twine("  printf_global_noncall_refs=") +
          Twine(globalStats.nonCallRefs));
  message(Twine("  printf_global_address_taken_refs=") +
          Twine(globalStats.addressTakenRefs));
  message(Twine("  printf_global_direct_printf_core_routes=") +
          Twine(globalStats.directPrintfCoreRoutes));
  message(Twine("  printf_global_unrecognized_printf_core_routes=") +
          Twine(globalStats.unrecognizedPrintfCoreRoutes));
  message(Twine("  printf_global_unresolved_routes=") +
          Twine(globalStats.unresolvedRoutes));
  message(Twine("  printf_global_direct_entry_routes=") +
          Twine(globalStats.directEntryRoutes));
  message(Twine("  printf_global_matched_proof_routes=") +
          Twine(globalStats.matchedProofRoutes));
  message(Twine("  printf_global_missing_proof_routes=") +
          Twine(globalStats.missingProofRoutes));
  message(Twine("  printf_global_alias_routes=") +
          Twine(globalStats.aliasRoutes));
  message(Twine("  all_live_printf_core_entries_proven_non_float=") +
          Twine(globalStats.gateReady ? 1 : 0));
  message(Twine("  printf_core_float_helper_calls=") +
          Twine(printfCoreFloatCalls.size()));
  message(Twine("  printf_core_float_helper_unique_functions=") +
          Twine(printfCoreFloatHelpers.size()));
  message(Twine("  printf_core_float_candidate_regions=") +
          Twine(printfCoreFloatRegions.size()));
  message(Twine("  printf_core_float_candidate_bytes=") +
          Twine(printfCoreFloatCandidateBytes));
  message(Twine("  printf_core_float_region_internal_edges=") +
          Twine(printfCoreFloatInternalEdges));
  message(Twine("  printf_core_float_region_incoming_edges=") +
          Twine(printfCoreFloatIncomingEdges));
  message(Twine("  printf_core_float_region_outgoing_edges=") +
          Twine(printfCoreFloatOutgoingEdges));
  message(Twine("  printf_core_float_region_incoming_fallthrough_edges=") +
          Twine(printfCoreFloatIncomingFallthroughEdges));
  message(Twine("  printf_core_float_region_outgoing_fallthrough_edges=") +
          Twine(printfCoreFloatOutgoingFallthroughEdges));
  message(Twine("  printf_core_float_dispatch_candidates=") +
          Twine(printfCoreFloatDispatchCandidates));
  message(Twine("  printf_core_float_unknown_control_flow=") +
          Twine(printfCoreFloatUnknownControlFlow));
  message(Twine("  printf_core_float_region_helper_call_misses=") +
          Twine(printfCoreFloatHelperCallMisses));
  message(Twine("  printf_core_float_region_isolatable=") +
          Twine(printfCoreFloatRegionIsolatable ? 1 : 0));
  message(Twine("  candidate_float_format_seen=") +
          Twine(candidateFloatFormatSeen ? 1 : 0));
  message(Twine("  candidate_long_double_format_seen=") +
          Twine(candidateLongDoubleFormatSeen ? 1 : 0));
  message(Twine("  failed_callsite_dump_requested=") +
          Twine(failedCallsiteDumpRequested));
  message(Twine("  failed_callsite_dump_emitted=") +
          Twine(failedCallsiteDumpEmitted));
  message(Twine("  requested_call_offset_dumps=") +
          Twine(requestedCallOffsetDumps));
  message(Twine("  matched_call_offset_dumps=") +
          Twine(matchedCallOffsetDumps));
  message(Twine("  decoded_source_functions=") +
          Twine(perfStats.decodedSourceFunctions));
  message(Twine("  decoded_instruction_count=") +
          Twine(perfStats.decodedInstructionCount));
  message(Twine("  decode_cache_hits=") + Twine(perfStats.decodeCacheHits));
  message(Twine("  decode_cache_misses=") +
          Twine(perfStats.decodeCacheMisses));
  message(Twine("  reloc_cache_hits=") + Twine(perfStats.relocCacheHits));
  message(Twine("  reloc_cache_misses=") + Twine(perfStats.relocCacheMisses));
}
} // namespace

// Do actual linking. Note that when this function is called,
// all linker scripts have already been parsed.
void LinkerDriver::link(opt::InputArgList &args) {
  llvm::TimeTraceScope timeScope("Link", StringRef("LinkerDriver::Link"));
  // If a --hash-style option was not given, set to a default value,
  // which varies depending on the target.
  if (!args.hasArg(OPT_hash_style)) {
    if (config->emachine == EM_MIPS || config->emachine == EM_SW64)
      config->sysvHash = true;
    else
      config->sysvHash = config->gnuHash = true;
  }

  // Default output filename is "a.out" by the Unix tradition.
  if (config->outputFile.empty())
    config->outputFile = "a.out";

  // Fail early if the output file or map file is not writable. If a user has a
  // long link, e.g. due to a large LTO link, they do not wish to run it and
  // find that it failed because there was a mistake in their command-line.
  {
    llvm::TimeTraceScope timeScope("Create output files");
    if (auto e = tryCreateFile(config->outputFile))
      error("cannot open output file " + config->outputFile + ": " +
            e.message());
    if (auto e = tryCreateFile(config->mapFile))
      error("cannot open map file " + config->mapFile + ": " + e.message());
    if (auto e = tryCreateFile(config->whyExtract))
      error("cannot open --why-extract= file " + config->whyExtract + ": " +
            e.message());
  }
  if (errorCount())
    return;

  // Use default entry point name if no name was given via the command
  // line nor linker scripts. For some reason, MIPS entry point name is
  // different from others.
  config->warnMissingEntry =
      (!config->entry.empty() || (!config->shared && !config->relocatable));
  if (config->entry.empty() && !config->relocatable)
    config->entry = (config->emachine == EM_MIPS) ? "__start" : "_start";

  // Handle --trace-symbol.
  for (auto *arg : args.filtered(OPT_trace_symbol))
    symtab.insert(arg->getValue())->traced = true;

  // Handle -u/--undefined before input files. If both a.a and b.so define foo,
  // -u foo a.a b.so will extract a.a.
  for (StringRef name : config->undefined)
    addUnusedUndefined(name)->referenced = true;

  // Add all files to the symbol table. This will add almost all
  // symbols that we need to the symbol table. This process might
  // add files to the link, via autolinking, these files are always
  // appended to the Files vector.
  {
    llvm::TimeTraceScope timeScope("Parse input files");
    for (size_t i = 0; i < files.size(); ++i) {
      llvm::TimeTraceScope timeScope("Parse input files", files[i]->getName());
      parseFile(files[i]);
    }
    if (armCmseImpLib)
      parseArmCMSEImportLib(*armCmseImpLib);
  }

  // Now that we have every file, we can decide if we will need a
  // dynamic symbol table.
  // We need one if we were asked to export dynamic symbols or if we are
  // producing a shared library.
  // We also need one if any shared libraries are used and for pie executables
  // (probably because the dynamic linker needs it).
  config->hasDynSymTab =
      !ctx.sharedFiles.empty() || config->isPic || config->exportDynamic;

  // Some symbols (such as __ehdr_start) are defined lazily only when there
  // are undefined symbols for them, so we add these to trigger that logic.
  for (StringRef name : script->referencedSymbols) {
    Symbol *sym = addUnusedUndefined(name);
    sym->isUsedInRegularObj = true;
    sym->referenced = true;
  }

  // Prevent LTO from removing any definition referenced by -u.
  for (StringRef name : config->undefined)
    if (Defined *sym = dyn_cast_or_null<Defined>(symtab.find(name)))
      sym->isUsedInRegularObj = true;

  // If an entry symbol is in a static archive, pull out that file now.
  if (Symbol *sym = symtab.find(config->entry))
    handleUndefined(sym, "--entry");

  // Handle the `--undefined-glob <pattern>` options.
  for (StringRef pat : args::getStrings(args, OPT_undefined_glob))
    handleUndefinedGlob(pat);

  // Mark -init and -fini symbols so that the LTO doesn't eliminate them.
  if (Symbol *sym = dyn_cast_or_null<Defined>(symtab.find(config->init)))
    sym->isUsedInRegularObj = true;
  if (Symbol *sym = dyn_cast_or_null<Defined>(symtab.find(config->fini)))
    sym->isUsedInRegularObj = true;

  // If any of our inputs are bitcode files, the LTO code generator may create
  // references to certain library functions that might not be explicit in the
  // bitcode file's symbol table. If any of those library functions are defined
  // in a bitcode file in an archive member, we need to arrange to use LTO to
  // compile those archive members by adding them to the link beforehand.
  //
  // However, adding all libcall symbols to the link can have undesired
  // consequences. For example, the libgcc implementation of
  // __sync_val_compare_and_swap_8 on 32-bit ARM pulls in an .init_array entry
  // that aborts the program if the Linux kernel does not support 64-bit
  // atomics, which would prevent the program from running even if it does not
  // use 64-bit atomics.
  //
  // Therefore, we only add libcall symbols to the link before LTO if we have
  // to, i.e. if the symbol's definition is in bitcode. Any other required
  // libcall symbols will be added to the link after LTO when we add the LTO
  // object file to the link.
  if (!ctx.bitcodeFiles.empty())
    for (auto *s : lto::LTO::getRuntimeLibcallSymbols())
      handleLibcall(s);

  // Archive members defining __wrap symbols may be extracted.
  std::vector<WrappedSymbol> wrapped = addWrappedSymbols(args);

  // No more lazy bitcode can be extracted at this point. Do post parse work
  // like checking duplicate symbols.
  parallelForEach(ctx.objectFiles, [](ELFFileBase *file) {
    initSectionsAndLocalSyms(file, /*ignoreComdats=*/false);
  });
  parallelForEach(ctx.objectFiles, postParseObjectFile);
  parallelForEach(ctx.bitcodeFiles,
                  [](BitcodeFile *file) { file->postParse(); });
  for (auto &it : ctx.nonPrevailingSyms) {
    Symbol &sym = *it.first;
    Undefined(sym.file, sym.getName(), sym.binding, sym.stOther, sym.type,
              it.second)
        .overwrite(sym);
    cast<Undefined>(sym).nonPrevailing = true;
  }
  ctx.nonPrevailingSyms.clear();
  for (const DuplicateSymbol &d : ctx.duplicates)
    reportDuplicate(*d.sym, d.file, d.section, d.value);
  ctx.duplicates.clear();

  // Return if there were name resolution errors.
  if (errorCount())
    return;

  // We want to declare linker script's symbols early,
  // so that we can version them.
  // They also might be exported if referenced by DSOs.
  script->declareSymbols();

  // Handle --exclude-libs. This is before scanVersionScript() due to a
  // workaround for Android ndk: for a defined versioned symbol in an archive
  // without a version node in the version script, Android does not expect a
  // 'has undefined version' error in -shared --exclude-libs=ALL mode (PR36295).
  // GNU ld errors in this case.
  if (args.hasArg(OPT_exclude_libs))
    excludeLibs(args);

  // Create elfHeader early. We need a dummy section in
  // addReservedSymbols to mark the created symbols as not absolute.
  Out::elfHeader = make<OutputSection>("", 0, SHF_ALLOC);

  // We need to create some reserved symbols such as _end. Create them.
  if (!config->relocatable)
    addReservedSymbols();

  // Apply version scripts.
  //
  // For a relocatable output, version scripts don't make sense, and
  // parsing a symbol version string (e.g. dropping "@ver1" from a symbol
  // name "foo@ver1") rather do harm, so we don't call this if -r is given.
  if (!config->relocatable) {
    llvm::TimeTraceScope timeScope("Process symbol versions");
    symtab.scanVersionScript();
  }

  // Skip the normal linked output if some LTO options are specified.
  //
  // For --thinlto-index-only, index file creation is performed in
  // compileBitcodeFiles, so we are done afterwards. --plugin-opt=emit-llvm and
  // --plugin-opt=emit-asm create output files in bitcode or assembly code,
  // respectively. When only certain thinLTO modules are specified for
  // compilation, the intermediate object file are the expected output.
  const bool skipLinkedOutput = config->thinLTOIndexOnly || config->emitLLVM ||
                                config->ltoEmitAsm ||
                                !config->thinLTOModulesToCompile.empty();

  // Handle --lto-validate-all-vtables-have-type-infos.
  if (config->ltoValidateAllVtablesHaveTypeInfos)
    invokeELFT(ltoValidateAllVtablesHaveTypeInfos, args);

  // Do link-time optimization if given files are LLVM bitcode files.
  // This compiles bitcode files into real object files.
  //
  // With this the symbol table should be complete. After this, no new names
  // except a few linker-synthesized ones will be added to the symbol table.
  const size_t numObjsBeforeLTO = ctx.objectFiles.size();
  invokeELFT(compileBitcodeFiles, skipLinkedOutput);

  // Symbol resolution finished. Report backward reference problems,
  // --print-archive-stats=, and --why-extract=.
  reportBackrefs();
  writeArchiveStats();
  writeWhyExtract();
#if defined(ENABLE_AUTOTUNER)
  // AUTO-TUNING - finalization
  if (Error E = autotuning::Engine.finalize()) {
    error(toString(std::move(E)));
  }
#endif
  if (errorCount())
    return;

  // Bail out if normal linked output is skipped due to LTO.
  if (skipLinkedOutput)
    return;

  // compileBitcodeFiles may have produced lto.tmp object files. After this, no
  // more file will be added.
  auto newObjectFiles = ArrayRef(ctx.objectFiles).slice(numObjsBeforeLTO);
  parallelForEach(newObjectFiles, [](ELFFileBase *file) {
    initSectionsAndLocalSyms(file, /*ignoreComdats=*/true);
  });
  parallelForEach(newObjectFiles, postParseObjectFile);
  for (const DuplicateSymbol &d : ctx.duplicates)
    reportDuplicate(*d.sym, d.file, d.section, d.value);

  // Handle --exclude-libs again because lto.tmp may reference additional
  // libcalls symbols defined in an excluded archive. This may override
  // versionId set by scanVersionScript().
  if (args.hasArg(OPT_exclude_libs))
    excludeLibs(args);

  // Record [__acle_se_<sym>, <sym>] pairs for later processing.
  processArmCmseSymbols();

  // Apply symbol renames for --wrap and combine foo@v1 and foo@@v1.
  redirectSymbols(wrapped);

  // Replace common symbols with regular symbols.
  replaceCommonSymbols();

  // Phase 0 of RISC-V function-level InputSection splitting only audits
  // candidates. It must run after ObjFile::postParse() has assigned Defined
  // symbols to sections and before original sections are aggregated.
  invokeELFT(auditRISCVFunctionSectionsSplit,);

  {
    llvm::TimeTraceScope timeScope("Aggregate sections");
    // Now that we have a complete list of input files.
    // Beyond this point, no new files are added.
    // Aggregate all input sections into one place.
    for (InputFile *f : ctx.objectFiles) {
      for (InputSectionBase *s : f->getSections()) {
        if (!s || s == &InputSection::discarded)
          continue;
        auto splitIt = riscvFunctionSplitChildren.find(s);
        if (splitIt != riscvFunctionSplitChildren.end()) {
          for (InputSectionBase *child : splitIt->second)
            ctx.inputSections.push_back(child);
          continue;
        }
        if (LLVM_UNLIKELY(isa<EhInputSection>(s)))
          ctx.ehInputSections.push_back(cast<EhInputSection>(s));
        else
          ctx.inputSections.push_back(s);
      }
    }
    for (BinaryFile *f : ctx.binaryFiles)
      for (InputSectionBase *s : f->getSections())
        ctx.inputSections.push_back(cast<InputSection>(s));
  }

  {
    llvm::TimeTraceScope timeScope("Strip sections");
    if (ctx.hasSympart.load(std::memory_order_relaxed)) {
      llvm::erase_if(ctx.inputSections, [](InputSectionBase *s) {
        if (s->type != SHT_LLVM_SYMPART)
          return false;
        invokeELFT(readSymbolPartitionSection, s);
        return true;
      });
    }
    // We do not want to emit debug sections if --strip-all
    // or --strip-debug are given.
    if (config->strip != StripPolicy::None) {
      llvm::erase_if(ctx.inputSections, [](InputSectionBase *s) {
        if (isDebugSection(*s))
          return true;
        if (auto *isec = dyn_cast<InputSection>(s))
          if (InputSectionBase *rel = isec->getRelocatedSection())
            if (isDebugSection(*rel))
              return true;

        return false;
      });
    }
  }

  // Since we now have a complete set of input files, we can create
  // a .d file to record build dependencies.
  if (!config->dependencyFile.empty())
    writeDependencyFile();

  // Now that the number of partitions is fixed, save a pointer to the main
  // partition.
  mainPart = &partitions[0];

  // Read .note.gnu.property sections from input object files which
  // contain a hint to tweak linker's and loader's behaviors.
  config->andFeatures = getAndFeatures();

  // The Target instance handles target-specific stuff, such as applying
  // relocations or writing a PLT section. It also contains target-dependent
  // values such as a default image base address.
  target = getTarget();

  config->eflags = target->calcEFlags();
  // maxPageSize (sometimes called abi page size) is the maximum page size that
  // the output can be run on. For example if the OS can use 4k or 64k page
  // sizes then maxPageSize must be 64k for the output to be useable on both.
  // All important alignment decisions must use this value.
  config->maxPageSize = getMaxPageSize(args);
  // commonPageSize is the most common page size that the output will be run on.
  // For example if an OS can use 4k or 64k page sizes and 4k is more common
  // than 64k then commonPageSize is set to 4k. commonPageSize can be used for
  // optimizations such as DATA_SEGMENT_ALIGN in linker scripts. LLD's use of it
  // is limited to writing trap instructions on the last executable segment.
  config->commonPageSize = getCommonPageSize(args);

  config->imageBase = getImageBase(args);

  // This adds a .comment section containing a version string.
  if (!config->relocatable)
    ctx.inputSections.push_back(createCommentSection());

  // Split SHF_MERGE and .eh_frame sections into pieces in preparation for garbage collection.
  invokeELFT(splitSections,);
  invokeELFT(runRISCVPrintfSpecializationPreGC,);

  // Garbage collection and removal of shared symbols from unused shared objects.
  invokeELFT(markLive,);
  printRISCVFunctionSplitGCStats();
  invokeELFT(printRISCVLibcSpecializationAudit,);
  demoteSharedAndLazySymbols();

  // Make copies of any input sections that need to be copied into each
  // partition.
  copySectionsIntoPartitions();

  // Create synthesized sections such as .got and .plt. This is called before
  // processSectionCommands() so that they can be placed by SECTIONS commands.
  invokeELFT(createSyntheticSections,);

  // Some input sections that are used for exception handling need to be moved
  // into synthetic sections. Do that now so that they aren't assigned to
  // output sections in the usual way.
  if (!config->relocatable)
    combineEhSections();

  // Merge .riscv.attributes sections.
  if (config->emachine == EM_RISCV)
    mergeRISCVAttributesSections();

  {
    llvm::TimeTraceScope timeScope("Assign sections");

    // Create output sections described by SECTIONS commands.
    script->processSectionCommands();

    // Linker scripts control how input sections are assigned to output
    // sections. Input sections that were not handled by scripts are called
    // "orphans", and they are assigned to output sections by the default rule.
    // Process that.
    script->addOrphanSections();
  }

  {
    llvm::TimeTraceScope timeScope("Merge/finalize input sections");

    // Migrate InputSectionDescription::sectionBases to sections. This includes
    // merging MergeInputSections into a single MergeSyntheticSection. From this
    // point onwards InputSectionDescription::sections should be used instead of
    // sectionBases.
    for (SectionCommand *cmd : script->sectionCommands)
      if (auto *osd = dyn_cast<OutputDesc>(cmd))
        osd->osec.finalizeInputSections();
  }

  // Two input sections with different output sections should not be folded.
  // ICF runs after processSectionCommands() so that we know the output sections.
  if (config->icf != ICFLevel::None) {
    invokeELFT(findKeepUniqueSections, args);
    invokeELFT(doIcf,);
  }

  // Read the callgraph now that we know what was gced or icfed
  if (config->callGraphProfileSort != CGProfileSortKind::None) {
    if (auto *arg = args.getLastArg(OPT_call_graph_ordering_file))
      if (std::optional<MemoryBufferRef> buffer = readFile(arg->getValue()))
        readCallGraph(*buffer);
    invokeELFT(readCallGraphsFromObjectFiles,);
  }

  // Write the result to the file.
  invokeELFT(writeResult,);
}
