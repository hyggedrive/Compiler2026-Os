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
  config->printRISCVConfigSpecializationAudit =
      args.hasArg(OPT_print_riscv_config_specialization_audit);
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

enum class RISCVConfigInsnKind {
  Unknown,
  CAddi,
  CLi,
  CLui,
  CMv,
  CAdd,
  CSlli,
  CSrli,
  CSrai,
  CAndi,
  CSub,
  CXor,
  COr,
  CAnd,
  CLw,
  CLwsp,
  CSwsp,
  CControlFlow,
  Addi,
  Lui,
  Auipc,
  Load,
  Store,
  ControlFlow,
  Op,
};

static StringRef riscvConfigInsnKindName(RISCVConfigInsnKind kind) {
  switch (kind) {
  case RISCVConfigInsnKind::Unknown:
    return "unknown";
  case RISCVConfigInsnKind::CAddi:
    return "c.addi";
  case RISCVConfigInsnKind::CLi:
    return "c.li";
  case RISCVConfigInsnKind::CLui:
    return "c.lui";
  case RISCVConfigInsnKind::CMv:
    return "c.mv";
  case RISCVConfigInsnKind::CAdd:
    return "c.add";
  case RISCVConfigInsnKind::CSlli:
    return "c.slli";
  case RISCVConfigInsnKind::CSrli:
    return "c.srli";
  case RISCVConfigInsnKind::CSrai:
    return "c.srai";
  case RISCVConfigInsnKind::CAndi:
    return "c.andi";
  case RISCVConfigInsnKind::CSub:
    return "c.sub";
  case RISCVConfigInsnKind::CXor:
    return "c.xor";
  case RISCVConfigInsnKind::COr:
    return "c.or";
  case RISCVConfigInsnKind::CAnd:
    return "c.and";
  case RISCVConfigInsnKind::CLw:
    return "c.lw";
  case RISCVConfigInsnKind::CLwsp:
    return "c.lwsp";
  case RISCVConfigInsnKind::CSwsp:
    return "c.swsp";
  case RISCVConfigInsnKind::CControlFlow:
    return "c.control-flow";
  case RISCVConfigInsnKind::Addi:
    return "addi";
  case RISCVConfigInsnKind::Lui:
    return "lui";
  case RISCVConfigInsnKind::Auipc:
    return "auipc";
  case RISCVConfigInsnKind::Load:
    return "load";
  case RISCVConfigInsnKind::Store:
    return "store";
  case RISCVConfigInsnKind::ControlFlow:
    return "control-flow";
  case RISCVConfigInsnKind::Op:
    return "op";
  }
  llvm_unreachable("invalid RISC-V config instruction kind");
}

struct RISCVConfigInsn {
  uint64_t off = 0;
  uint32_t raw = 0;
  uint8_t size = 0;
  RISCVConfigInsnKind kind = RISCVConfigInsnKind::Unknown;
  bool controlFlow = false;
  bool call = false;
  bool load = false;
  bool store = false;
  int rd = -1;
  int rs1 = -1;
  int rs2 = -1;
  int64_t imm = 0;
};

static RISCVConfigInsn decodeRISCVConfigInsn(ArrayRef<uint8_t> data,
                                             uint64_t off) {
  RISCVConfigInsn insn;
  insn.off = off;
  if (off + 2 > data.size())
    return insn;
  uint16_t half = llvm::support::endian::read16le(data.data() + off);
  if ((half & 3) != 3) {
    insn.raw = half;
    insn.size = 2;
    uint32_t quadrant = half & 3;
    uint32_t funct3 = bits(half, 15, 13);
    if (quadrant == 0 && funct3 == 2) {
      insn.kind = RISCVConfigInsnKind::CLw;
      insn.load = true;
      insn.rd = 8 + bits(half, 4, 2);
      insn.rs1 = 8 + bits(half, 9, 7);
      insn.imm = (bits(half, 5, 5) << 6) | (bits(half, 12, 10) << 3) |
                 (bits(half, 6, 6) << 2);
    } else if (quadrant == 1 && funct3 == 0) {
      insn.kind = RISCVConfigInsnKind::CAddi;
      insn.rd = bits(half, 11, 7);
      insn.rs1 = insn.rd;
      insn.imm =
          SignExtend64<6>((bits(half, 12, 12) << 5) | bits(half, 6, 2));
    } else if (quadrant == 1 && funct3 == 2) {
      insn.kind = RISCVConfigInsnKind::CLi;
      insn.rd = bits(half, 11, 7);
      insn.rs1 = 0;
      insn.imm =
          SignExtend64<6>((bits(half, 12, 12) << 5) | bits(half, 6, 2));
    } else if (quadrant == 1 && funct3 == 3) {
      insn.rd = bits(half, 11, 7);
      if (insn.rd == 2) {
        insn.kind = RISCVConfigInsnKind::CAddi;
        insn.rs1 = 2;
        insn.imm = SignExtend64<10>((bits(half, 12, 12) << 9) |
                                    (bits(half, 4, 3) << 7) |
                                    (bits(half, 5, 5) << 6) |
                                    (bits(half, 2, 2) << 5) |
                                    (bits(half, 6, 6) << 4));
      } else {
        insn.kind = RISCVConfigInsnKind::CLui;
        insn.imm = SignExtend64<18>((bits(half, 12, 12) << 17) |
                                    (bits(half, 6, 2) << 12));
      }
    } else if (quadrant == 1 && funct3 == 4) {
      uint32_t op = bits(half, 11, 10);
      insn.rd = 8 + bits(half, 9, 7);
      insn.rs1 = insn.rd;
      if (op == 0) {
        if (bits(half, 12, 12) != 0) {
          insn.kind = RISCVConfigInsnKind::Unknown;
        } else {
          insn.kind = RISCVConfigInsnKind::CSrli;
          insn.imm = (bits(half, 12, 12) << 5) | bits(half, 6, 2);
        }
      } else if (op == 1) {
        if (bits(half, 12, 12) != 0) {
          insn.kind = RISCVConfigInsnKind::Unknown;
        } else {
          insn.kind = RISCVConfigInsnKind::CSrai;
          insn.imm = (bits(half, 12, 12) << 5) | bits(half, 6, 2);
        }
      } else if (op == 2) {
        insn.kind = RISCVConfigInsnKind::CAndi;
        insn.imm =
            SignExtend64<6>((bits(half, 12, 12) << 5) | bits(half, 6, 2));
      } else {
        insn.rs2 = 8 + bits(half, 4, 2);
        if (bits(half, 12, 12) != 0) {
          insn.kind = RISCVConfigInsnKind::Unknown;
        } else {
          switch (bits(half, 6, 5)) {
          case 0:
            insn.kind = RISCVConfigInsnKind::CSub;
            break;
          case 1:
            insn.kind = RISCVConfigInsnKind::CXor;
            break;
          case 2:
            insn.kind = RISCVConfigInsnKind::COr;
            break;
          case 3:
            insn.kind = RISCVConfigInsnKind::CAnd;
            break;
          }
        }
      }
    } else if (quadrant == 2 && funct3 == 0) {
      insn.rd = bits(half, 11, 7);
      insn.rs1 = insn.rd;
      if (insn.rd != 0 && bits(half, 12, 12) == 0) {
        insn.kind = RISCVConfigInsnKind::CSlli;
        insn.imm = bits(half, 6, 2);
      }
    } else if (quadrant == 2 && funct3 == 4) {
      insn.rd = bits(half, 11, 7);
      insn.rs1 = insn.rd;
      insn.rs2 = bits(half, 6, 2);
      if (bits(half, 12, 12) == 0 && insn.rs2 != 0 && insn.rd != 0) {
        insn.kind = RISCVConfigInsnKind::CMv;
      } else if (bits(half, 12, 12) == 1 && insn.rs2 != 0 &&
                 insn.rd != 0) {
        insn.kind = RISCVConfigInsnKind::CAdd;
      } else if (insn.rs2 == 0) {
        insn.kind = RISCVConfigInsnKind::CControlFlow;
        insn.controlFlow = true;
      }
    } else if (quadrant == 2 && funct3 == 2) {
      insn.kind = RISCVConfigInsnKind::CLwsp;
      insn.load = true;
      insn.rd = bits(half, 11, 7);
      insn.rs1 = 2;
      insn.imm = (bits(half, 3, 2) << 6) | (bits(half, 12, 12) << 5) |
                 (bits(half, 6, 4) << 2);
    } else if (quadrant == 2 && funct3 == 6) {
      insn.kind = RISCVConfigInsnKind::CSwsp;
      insn.store = true;
      insn.rs1 = 2;
      insn.rs2 = bits(half, 6, 2);
      insn.imm = (bits(half, 8, 7) << 6) | (bits(half, 12, 9) << 2);
    } else if (quadrant == 1 &&
               (funct3 == 1 || funct3 == 5 || funct3 == 6 || funct3 == 7)) {
      insn.kind = RISCVConfigInsnKind::CControlFlow;
      insn.controlFlow = true;
    }
    return insn;
  }
  if (off + 4 > data.size())
    return insn;
  uint32_t word = llvm::support::endian::read32le(data.data() + off);
  insn.raw = word;
  insn.size = 4;
  uint32_t opcode = word & 0x7f;
  insn.rd = bits(word, 11, 7);
  insn.rs1 = bits(word, 19, 15);
  insn.rs2 = bits(word, 24, 20);
  switch (opcode) {
  case 0x13:
    insn.kind = RISCVConfigInsnKind::Addi;
    insn.imm = SignExtend64<12>(bits(word, 31, 20));
    break;
  case 0x37:
    insn.kind = RISCVConfigInsnKind::Lui;
    insn.rs1 = -1;
    insn.rs2 = -1;
    insn.imm = SignExtend64<32>(word & 0xfffff000);
    break;
  case 0x17:
    insn.kind = RISCVConfigInsnKind::Auipc;
    insn.rs1 = -1;
    insn.rs2 = -1;
    insn.imm = SignExtend64<32>(word & 0xfffff000);
    break;
  case 0x03:
    insn.kind = RISCVConfigInsnKind::Load;
    insn.load = true;
    insn.imm = SignExtend64<12>(bits(word, 31, 20));
    break;
  case 0x23:
    insn.kind = RISCVConfigInsnKind::Store;
    insn.store = true;
    insn.rd = -1;
    insn.imm =
        SignExtend64<12>((bits(word, 31, 25) << 5) | bits(word, 11, 7));
    break;
  case 0x63:
  case 0x6f:
  case 0x67:
    insn.kind = RISCVConfigInsnKind::ControlFlow;
    insn.controlFlow = true;
    break;
  case 0x33:
    insn.kind = RISCVConfigInsnKind::Op;
    break;
  default:
    break;
  }
  return insn;
}

static bool isRISCVConfigDirectCallRel(RelType type) {
  return type == R_RISCV_CALL || type == R_RISCV_CALL_PLT ||
         type == R_RISCV_JAL;
}

template <class ELFT, class RelTy>
static Defined *getRISCVConfigRelocTarget(InputSectionBase &sec,
                                          const RelTy &rel) {
  Symbol &sym = sec.getFile<ELFT>()->getRelocTargetSym(rel);
  return dyn_cast<Defined>(&sym);
}

template <class ELFT, class RelTy>
static bool riscvConfigRelocTargetsObject(InputSectionBase &sec,
                                          const RelTy &rel, Defined &object) {
  Defined *d = getRISCVConfigRelocTarget<ELFT>(sec, rel);
  if (!d)
    return false;
  auto *targetSec = dyn_cast_or_null<InputSectionBase>(d->section);
  if (!targetSec || targetSec != object.section)
    return false;
  uint64_t targetOff = 0;
  if (!checkedAddend(d->value, getRISCVFunctionSplitAddend(rel), targetOff))
    return false;
  uint64_t objectEnd = object.size ? object.value + object.size : object.value + 1;
  return targetOff >= object.value && targetOff < objectEnd;
}

template <class ELFT>
static Defined *findUniqueRISCVConfigDefinedByName(StringRef name,
                                                   uint8_t type,
                                                   bool &ambiguous) {
  Defined *found = nullptr;
  ambiguous = false;
  for (ELFFileBase *file : ctx.objectFiles) {
    for (Symbol *sym : file->getSymbols()) {
      Defined *d = dyn_cast_or_null<Defined>(sym);
      if (!d || d->type != type || d->isSection() || d->getName() != name)
        continue;
      if (found && found != d) {
        ambiguous = true;
        return nullptr;
      }
      found = d;
    }
  }
  return found;
}

struct RISCVConfigFunctionRef {
  Defined *sym = nullptr;
  std::string name;
  uint64_t begin = 0;
  uint64_t end = 0;
};

template <class ELFT>
static void dumpRISCVConfigResolverDebug(InputSectionBase &sec, uint64_t off) {
  InputSectionBase *parentSec = &sec;
  uint64_t originalBegin = 0;
  uint64_t originalEnd = sec.content().size();
  bool splitChild = false;
  auto storageIt = riscvFunctionSplitRelocStorage.find(&sec);
  if (storageIt != riscvFunctionSplitRelocStorage.end() &&
      storageIt->second.parent) {
    splitChild = true;
    parentSec = storageIt->second.parent;
    originalBegin = storageIt->second.originalBegin;
    originalEnd = storageIt->second.originalEnd;
  }
  message(Twine("riscv-config-resolver-debug: file=") + toString(sec.file) +
          " query_section=" + sec.name +
          " query_section_ptr=0x" +
          Twine::utohexstr(reinterpret_cast<uintptr_t>(&sec)) +
          " query_offset=0x" + Twine::utohexstr(off) +
          " split_child=" + Twine(splitChild ? 1 : 0) +
          " parent_section=" + (parentSec ? parentSec->name : StringRef("none")) +
          " parent_section_ptr=0x" +
          Twine::utohexstr(reinterpret_cast<uintptr_t>(parentSec)) +
          " original_begin=0x" + Twine::utohexstr(originalBegin) +
          " original_end=0x" + Twine::utohexstr(originalEnd));
  for (ELFFileBase *file : ctx.objectFiles) {
    if (file != sec.file)
      continue;
    for (Symbol *sym : file->getSymbols()) {
      Defined *d = dyn_cast_or_null<Defined>(sym);
      if (!d || d->type != STT_FUNC || d->isSection())
        continue;
      auto *symSec = dyn_cast_or_null<InputSectionBase>(d->section);
      if (!symSec)
        continue;
      auto childIt = riscvFunctionSplitRelocStorage.find(symSec);
      bool symIsChild = childIt != riscvFunctionSplitRelocStorage.end() &&
                        childIt->second.parent;
      message(Twine("riscv-config-resolver-debug: candidate name=") +
              d->getName() +
              " binding=" + (d->isLocal() ? Twine("local") : Twine("global")) +
              " section=" + symSec->name +
              " section_ptr=0x" +
              Twine::utohexstr(reinterpret_cast<uintptr_t>(symSec)) +
              " value=0x" + Twine::utohexstr(d->value) +
              " size=" + Twine(d->size) +
              " child=" + Twine(symIsChild ? 1 : 0) +
              " parent=" +
              (symIsChild ? childIt->second.parent->name : StringRef("none")) +
              " child_original_begin=0x" +
              Twine::utohexstr(symIsChild ? childIt->second.originalBegin : 0) +
              " child_original_end=0x" +
              Twine::utohexstr(symIsChild ? childIt->second.originalEnd : 0));
    }
  }
}

template <class ELFT>
static RISCVConfigFunctionRef
resolveRISCVFunctionForLocation(InputSectionBase &sec, uint64_t off) {
  RISCVConfigFunctionRef best;
  InputSectionBase *parentSec = &sec;
  uint64_t parentOff = off;
  auto storageIt = riscvFunctionSplitRelocStorage.find(&sec);
  if (storageIt != riscvFunctionSplitRelocStorage.end() &&
      storageIt->second.parent) {
    parentSec = storageIt->second.parent;
    parentOff = storageIt->second.originalBegin + off;
  }

  auto tryChild = [&](InputSectionBase *child,
                      const RISCVFunctionSplitRelocStorage &storage)
      -> std::optional<RISCVConfigFunctionRef> {
    if (off < storage.originalBegin || off >= storage.originalEnd)
      return std::nullopt;
    uint64_t childOff = off - storage.originalBegin;
    RISCVConfigFunctionRef childBest;
    for (ELFFileBase *file : ctx.objectFiles) {
      if (file != sec.file)
        continue;
      for (Symbol *sym : file->getSymbols()) {
        Defined *d = dyn_cast_or_null<Defined>(sym);
        if (!d || d->type != STT_FUNC || d->isSection() ||
            d->section != child)
          continue;
        uint64_t begin = d->value;
        uint64_t end = d->size ? d->value + d->size : child->content().size();
        if (childOff < begin || childOff >= end)
          continue;
        if (!childBest.sym || end - begin < childBest.end - childBest.begin)
          childBest = {d, d->getName().str(), begin, end};
      }
    }
    if (childBest.sym)
      return childBest;
    return std::nullopt;
  };

  auto childIt = riscvFunctionSplitChildren.find(&sec);
  if (childIt != riscvFunctionSplitChildren.end()) {
    std::optional<RISCVConfigFunctionRef> childBest;
    bool ambiguous = false;
    for (InputSectionBase *child : childIt->second) {
      auto st = riscvFunctionSplitRelocStorage.find(child);
      if (st == riscvFunctionSplitRelocStorage.end())
        continue;
      std::optional<RISCVConfigFunctionRef> r = tryChild(child, st->second);
      if (!r)
        continue;
      if (childBest && childBest->sym != r->sym)
        ambiguous = true;
      childBest = r;
    }
    if (childBest && !ambiguous)
      return *childBest;
    if (ambiguous)
      return {nullptr, "ambiguous-function", 0, sec.content().size()};
  }

  SmallVector<Defined *, 0> funcs;
  for (ELFFileBase *file : ctx.objectFiles) {
    if (file != sec.file)
      continue;
    for (Symbol *sym : file->getSymbols()) {
      Defined *d = dyn_cast_or_null<Defined>(sym);
      if (!d || d->type != STT_FUNC || d->isSection())
        continue;
      if (d->section != &sec && d->section != parentSec)
        continue;
      funcs.push_back(d);
    }
  }
  llvm::sort(funcs, [](Defined *a, Defined *b) {
    if (a->value != b->value)
      return a->value < b->value;
    return a->getName() < b->getName();
  });
  for (auto [i, d] : llvm::enumerate(funcs)) {
    bool useParentOffset = d->section == parentSec && parentSec != &sec;
    uint64_t queryOff = useParentOffset ? parentOff : off;
    uint64_t begin = d->value;
    auto *symSec = dyn_cast_or_null<InputSectionBase>(d->section);
    uint64_t secSize = symSec ? symSec->content().size() : 0;
    uint64_t end = d->size ? d->value + d->size : secSize;
    if (d->size == 0)
      for (size_t j = i + 1, e = funcs.size(); j != e; ++j)
        if (funcs[j]->section == d->section && funcs[j]->value > begin) {
          end = funcs[j]->value;
          break;
        }
    if (queryOff < begin || queryOff >= end)
      continue;
    if (!best.sym || end - begin < best.end - best.begin) {
      uint64_t localBegin = begin;
      uint64_t localEnd = end;
      if (useParentOffset) {
        if (end <= storageIt->second.originalBegin ||
            begin >= storageIt->second.originalEnd)
          continue;
        localBegin =
            begin > storageIt->second.originalBegin
                ? begin - storageIt->second.originalBegin
                : 0;
        localEnd = std::min(end, storageIt->second.originalEnd) -
                   storageIt->second.originalBegin;
      }
      best = {d, d->getName().str(), localBegin, localEnd};
    }
  }
  if (best.sym)
    return best;

  best.name = "unresolved-function";
  best.begin = 0;
  best.end = sec.content().size();
  return best;
}

static bool proveRISCVConfigRegConst(ArrayRef<RISCVConfigInsn> insns,
                                     uint64_t callOff, int reg, int64_t &value,
                                     std::string &reason) {
  for (auto it = insns.rbegin(), e = insns.rend(); it != e; ++it) {
    const RISCVConfigInsn &insn = *it;
    if (insn.off >= callOff)
      continue;
    if (insn.call) {
      reason = "call-clobber";
      return false;
    }
    if (insn.rd != reg)
      continue;
      if (insn.size == 2) {
        if (insn.kind == RISCVConfigInsnKind::CLi) {
          value = insn.imm;
          reason = "constant";
          return true;
        }
        if (insn.kind == RISCVConfigInsnKind::CAddi && insn.rs1 == reg) {
          int64_t base = 0;
        if (!proveRISCVConfigRegConst(insns, insn.off, reg, base, reason))
          return false;
        value = base + insn.imm;
        reason = "constant";
        return true;
      }
      reason = "unsupported-compressed-definition";
      return false;
    }
    uint32_t opcode = insn.raw & 0x7f;
    if (opcode == 0x13 && bits(insn.raw, 14, 12) == 0) {
      if (insn.rs1 == 0) {
        value = insn.imm;
        reason = "constant";
        return true;
      }
      int64_t base = 0;
      if (!proveRISCVConfigRegConst(insns, insn.off, insn.rs1, base, reason))
        return false;
      value = base + insn.imm;
      reason = "constant";
      return true;
    }
    if (opcode == 0x37) {
      value = insn.imm;
      reason = "constant";
      return true;
    }
    reason = insn.load ? "load-definition" : "unsupported-definition";
    return false;
  }
  reason = "definition-not-found";
  return false;
}

static bool convertRISCVConfigTargetOffset(InputSectionBase &evalSec,
                                           InputSectionBase &targetSec,
                                           uint64_t targetOff,
                                           uint64_t &evalOff);

struct RISCVConfigCallRecord {
  std::string callee;
  std::string caller;
  uint64_t callOffset = 0;
  bool arg0Proven = false;
  bool arg1Proven = false;
  int64_t arg0Value = 0;
  int64_t arg1Value = 0;
  std::string reason;
};

template <class ELFT>
static void printRISCVConfigCallsiteAudit(
    StringRef calleeName, SmallVectorImpl<RISCVConfigCallRecord> &records) {
  for (ELFFileBase *file : ctx.objectFiles) {
    for (InputSectionBase *sec : file->getSections()) {
      if (!sec || !sec->isLive() || !(sec->flags & SHF_EXECINSTR) ||
          !sec->file)
        continue;
      RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
      auto scan = [&](auto relsRange) {
        for (const auto &rel : relsRange) {
          RelType type = rel.getType(config->isMips64EL);
          if (!isRISCVConfigDirectCallRel(type))
            continue;
          Defined *target = getRISCVConfigRelocTarget<ELFT>(*sec, rel);
          if (!target || target->getName() != calleeName)
            continue;
          uint64_t off = rel.r_offset;
          RISCVConfigFunctionRef caller =
              resolveRISCVFunctionForLocation<ELFT>(*sec, off);
          if (!caller.sym)
            dumpRISCVConfigResolverDebug<ELFT>(*sec, off);
          InputSectionBase *decodeSec = &*sec;
          uint64_t decodeOff = off;
          bool coordOk = true;
          if (caller.sym) {
            auto *callerSec =
                dyn_cast_or_null<InputSectionBase>(caller.sym->section);
            if (callerSec && callerSec != sec) {
              coordOk = convertRISCVConfigTargetOffset(*callerSec, *sec, off,
                                                       decodeOff);
              if (coordOk)
                decodeSec = callerSec;
            }
          }
          ArrayRef<uint8_t> decodeData = decodeSec->content();
          DenseSet<uint64_t> decodeCallRelocOffsets;
          auto collectDecodeCallRelocs = [&](auto relRange) {
            for (const auto &callRel : relRange) {
              if (!isRISCVConfigDirectCallRel(
                      callRel.getType(config->isMips64EL)))
                continue;
              uint64_t callOff = callRel.r_offset;
              if (decodeSec != sec &&
                  !convertRISCVConfigTargetOffset(*decodeSec, *sec,
                                                  callRel.r_offset, callOff))
                continue;
              decodeCallRelocOffsets.insert(callOff);
            }
          };
          collectDecodeCallRelocs(rels.rels);
          collectDecodeCallRelocs(rels.relas);
          uint64_t begin = caller.begin;
          uint64_t end = caller.end;
          SmallVector<RISCVConfigInsn, 0> insns;
          bool decodeOk = coordOk;
          for (uint64_t pos = begin; pos < end;) {
            RISCVConfigInsn insn = decodeRISCVConfigInsn(decodeData, pos);
            if (insn.size == 0 || pos + insn.size > end) {
              decodeOk = false;
              break;
            }
            insn.call = decodeCallRelocOffsets.contains(pos);
            insns.push_back(insn);
            if (pos == decodeOff)
              break;
            pos += insn.size;
          }
          RISCVConfigCallRecord rec;
          rec.callee = calleeName.str();
          rec.caller = caller.name;
          rec.callOffset = decodeOff;
          if (!decodeOk) {
            rec.reason = "decode-failed";
          } else {
            std::string reason0, reason1;
            rec.arg0Proven = proveRISCVConfigRegConst(
                insns, decodeOff, 10, rec.arg0Value, reason0);
            rec.arg1Proven = proveRISCVConfigRegConst(
                insns, decodeOff, 11, rec.arg1Value, reason1);
            rec.reason = (rec.arg0Proven && rec.arg1Proven)
                             ? "constant"
                             : (!rec.arg0Proven ? reason0 : reason1);
          }
          records.push_back(rec);
          message(Twine("riscv-config-callsite: callee=") + rec.callee +
                  " caller=" + rec.caller +
                  " call_offset=0x" + Twine::utohexstr(rec.callOffset) +
                  " arg0_proven=" + Twine(rec.arg0Proven ? 1 : 0) +
                  " arg0_value=" +
                  (rec.arg0Proven ? Twine(rec.arg0Value) : Twine("unknown")) +
                  " arg1_proven=" + Twine(rec.arg1Proven ? 1 : 0) +
                  " arg1_value=" +
                  (rec.arg1Proven ? Twine(rec.arg1Value) : Twine("unknown")) +
                  " reason=" + rec.reason);
        }
      };
      scan(rels.rels);
      scan(rels.relas);
    }
  }
}

struct RISCVConfigGlobalAudit {
  std::string name;
  uint64_t size = 0;
  uint32_t directReads = 0;
  uint32_t directWrites = 0;
  std::set<std::string> writerFunctions;
  bool addressTaken = false;
  bool unknownPointerUse = false;
  bool externalReferenceKnown = false;
};

struct RISCVConfigTrackedGlobal {
  Defined *sym = nullptr;
  std::string name;
  RISCVConfigGlobalAudit audit;
};

template <class ELFT>
static void auditRISCVConfigGlobal(StringRef name,
                                   RISCVConfigGlobalAudit &audit) {
  bool ambiguous = false;
  Defined *targetSym =
      findUniqueRISCVConfigDefinedByName<ELFT>(name, STT_OBJECT, ambiguous);
  if (!targetSym) {
    if (ambiguous)
      message(Twine("riscv-config-global: symbol=") + name +
              " ambiguous=1");
    return;
  }
  audit.name = name.str();
  audit.size = targetSym->size;
  for (ELFFileBase *file : ctx.objectFiles) {
    for (InputSectionBase *sec : file->getSections()) {
      if (!sec || !sec->isLive() || !(sec->flags & SHF_ALLOC) || !sec->file)
        continue;
      RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
      auto scan = [&](auto relsRange) {
        for (const auto &rel : relsRange) {
          if (!riscvConfigRelocTargetsObject<ELFT>(*sec, rel, *targetSym))
            continue;
          RelType type = rel.getType(config->isMips64EL);
          bool directAddress = type == R_RISCV_HI20 || type == R_RISCV_LO12_I ||
                               type == R_RISCV_LO12_S || type == R_RISCV_32;
          if (!directAddress) {
            audit.unknownPointerUse = true;
            continue;
          }
          if (!(sec->flags & SHF_EXECINSTR)) {
            audit.addressTaken = true;
            continue;
          }
          RISCVConfigInsn insn = decodeRISCVConfigInsn(sec->content(),
                                                       rel.r_offset);
          RISCVConfigFunctionRef writer =
              resolveRISCVFunctionForLocation<ELFT>(*sec, rel.r_offset);
          if (!writer.sym)
            dumpRISCVConfigResolverDebug<ELFT>(*sec, rel.r_offset);
          if (insn.store) {
            ++audit.directWrites;
            audit.writerFunctions.insert(writer.name);
          } else {
            ++audit.directReads;
          }
        }
      };
      scan(rels.rels);
      scan(rels.relas);
    }
  }
  bool candidateWriterSetSafe =
      !audit.addressTaken && !audit.unknownPointerUse &&
      !audit.writerFunctions.empty() && audit.writerFunctions.size() <= 2;
  SmallVector<std::string, 0> writers(audit.writerFunctions.begin(),
                                      audit.writerFunctions.end());
  message(Twine("riscv-config-global: symbol=") + audit.name +
          " size=" + Twine(audit.size) +
          " direct_reads=" + Twine(audit.directReads) +
          " direct_writes=" + Twine(audit.directWrites) +
          " writer_functions=" +
          (writers.empty() ? Twine("none") : Twine(llvm::join(writers, ","))) +
          " address_taken=" + Twine(audit.addressTaken ? 1 : 0) +
          " unknown_pointer_use=" + Twine(audit.unknownPointerUse ? 1 : 0) +
          " external_reference=" +
          (audit.externalReferenceKnown ? Twine("0") : Twine("unknown")) +
          " candidate_writer_set_safe=" +
          Twine(candidateWriterSetSafe ? 1 : 0) +
          " initialization_chain_proven=0");
}

struct RISCVConfigRodataAudit {
  std::string name;
  uint64_t size = 0;
  uint32_t liveReferenceCount = 0;
  std::set<std::string> referenceFunctions;
  bool addressTaken = false;
  bool dynamicIndex = false;
};

struct RISCVConfigProofResult {
  bool complete = false;
  std::string reason = "static-evaluator-not-started";
  std::string failFunction;
  uint64_t failOffset = 0;
  uint32_t failOpcode = 0;
  uint16_t failRaw16 = 0;
  uint8_t failQuadrant = 0;
  uint8_t failFunct3 = 0;
  uint8_t failBit12 = 0;
  int failRd = -1;
  int failRs2 = -1;
  RISCVConfigInsnKind failKind = RISCVConfigInsnKind::Unknown;
  uint32_t visitedBlocks = 0;
  uint32_t executedInstructions = 0;
  uint32_t loopIterations = 0;
  uint32_t readonlyLoads = 0;
  uint32_t directCalls = 0;
  uint32_t abstractCalls = 0;
  uint32_t trackedStores = 0;
  uint32_t functionsEvaluated = 0;
  uint32_t constantBranches = 0;
  uint32_t alwaysTakenBranches = 0;
  uint32_t neverTakenBranches = 0;
  uint32_t branchTraceEmitted = 0;
  std::map<std::string, std::optional<int64_t>> values;
  std::set<std::string> evaluatedFunctionNames;
  std::set<Defined *> readonlySourceObjects;
};

enum class RISCVConfigValueKind {
  Unknown,
  Integer,
  SymbolAddress,
  StackAddress,
};

struct RISCVConfigValue {
  RISCVConfigValueKind kind = RISCVConfigValueKind::Unknown;
  int64_t value = 0;
  Defined *symbol = nullptr;
  int64_t offset = 0;
};

struct RISCVConfigEvalState {
  std::array<RISCVConfigValue, 32> regs;
  DenseMap<int64_t, RISCVConfigValue> stackSlots;
  DenseMap<Defined *, RISCVConfigValue> trackedGlobals;
};

static RISCVConfigValue riscvConfigInteger(int64_t v) {
  RISCVConfigValue value;
  value.kind = RISCVConfigValueKind::Integer;
  value.value = v;
  return value;
}

static RISCVConfigValue riscvConfigSymbolAddress(Defined *sym, int64_t off) {
  RISCVConfigValue value;
  value.kind = RISCVConfigValueKind::SymbolAddress;
  value.symbol = sym;
  value.offset = off;
  return value;
}

static RISCVConfigValue riscvConfigStackAddress(int64_t off) {
  RISCVConfigValue value;
  value.kind = RISCVConfigValueKind::StackAddress;
  value.offset = off;
  return value;
}

static bool riscvConfigAddValues(const RISCVConfigValue &a,
                                 const RISCVConfigValue &b,
                                 RISCVConfigValue &out) {
  if (a.kind == RISCVConfigValueKind::Integer &&
      b.kind == RISCVConfigValueKind::Integer) {
    out = riscvConfigInteger(a.value + b.value);
    return true;
  }
  if (a.kind == RISCVConfigValueKind::SymbolAddress &&
      b.kind == RISCVConfigValueKind::Integer) {
    out = riscvConfigSymbolAddress(a.symbol, a.offset + b.value);
    return true;
  }
  if (a.kind == RISCVConfigValueKind::Integer &&
      b.kind == RISCVConfigValueKind::SymbolAddress) {
    out = riscvConfigSymbolAddress(b.symbol, b.offset + a.value);
    return true;
  }
  if (a.kind == RISCVConfigValueKind::StackAddress &&
      b.kind == RISCVConfigValueKind::Integer) {
    out = riscvConfigStackAddress(a.offset + b.value);
    return true;
  }
  if (a.kind == RISCVConfigValueKind::Integer &&
      b.kind == RISCVConfigValueKind::StackAddress) {
    out = riscvConfigStackAddress(b.offset + a.value);
    return true;
  }
  return false;
}

static bool riscvConfigSubInteger(const RISCVConfigValue &a, int64_t b,
                                  RISCVConfigValue &out) {
  if (a.kind == RISCVConfigValueKind::Integer) {
    out = riscvConfigInteger(a.value - b);
    return true;
  }
  if (a.kind == RISCVConfigValueKind::SymbolAddress) {
    out = riscvConfigSymbolAddress(a.symbol, a.offset - b);
    return true;
  }
  if (a.kind == RISCVConfigValueKind::StackAddress) {
    out = riscvConfigStackAddress(a.offset - b);
    return true;
  }
  return false;
}

struct RISCVConfigBasicBlock {
  uint64_t begin = 0;
  uint64_t end = 0;
  SmallVector<RISCVConfigInsn, 0> insns;
};

struct RISCVConfigRelocInfo {
  RelType type = static_cast<RelType>(0);
  Defined *target = nullptr;
  int64_t addend = 0;
};

template <class ELFT>
static DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>>
getRISCVConfigRelocs(InputSectionBase &sec) {
  DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> result;
  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  auto scan = [&](auto relRange) {
    for (const auto &rel : relRange) {
      RISCVConfigRelocInfo info;
      info.type = rel.getType(config->isMips64EL);
      info.target = getRISCVConfigRelocTarget<ELFT>(sec, rel);
      info.addend = getRISCVFunctionSplitAddend(rel);
      result[rel.r_offset].push_back(info);
    }
  };
  scan(rels.rels);
  scan(rels.relas);
  return result;
}

static const RISCVConfigRelocInfo *
findRISCVConfigReloc(ArrayRef<RISCVConfigRelocInfo> relocs,
                     ArrayRef<RelType> types) {
  const RISCVConfigRelocInfo *found = nullptr;
  for (const RISCVConfigRelocInfo &r : relocs) {
    if (!llvm::is_contained(types, r.type))
      continue;
    if (found)
      return nullptr;
    found = &r;
  }
  return found;
}

static bool readRISCVConfigReadonlyByte(Defined *sym, int64_t offset,
                                        uint8_t &value,
                                        std::string &reason) {
  if (!sym || sym->type != STT_OBJECT) {
    reason = "readonly-load-non-object";
    return false;
  }
  auto *sec = dyn_cast_or_null<InputSectionBase>(sym->section);
  if (!sec) {
    reason = "readonly-load-no-section";
    return false;
  }
  if (sec->flags & SHF_WRITE) {
    reason = "readonly-load-writable";
    return false;
  }
  if (offset < 0 || static_cast<uint64_t>(offset) >= sym->size) {
    reason = "readonly-load-out-of-object";
    return false;
  }
  uint64_t secOff = sym->value + static_cast<uint64_t>(offset);
  if (secOff >= sec->content().size()) {
    reason = "readonly-load-out-of-section";
    return false;
  }
  value = sec->content()[secOff];
  return true;
}

static bool isRISCVConfigTrackedObject(
    Defined *sym, ArrayRef<RISCVConfigTrackedGlobal> globals,
    const RISCVConfigTrackedGlobal **tracked = nullptr) {
  for (const RISCVConfigTrackedGlobal &g : globals) {
    if (g.sym != sym)
      continue;
    if (tracked)
      *tracked = &g;
    return true;
  }
  return false;
}

static bool resolveRISCVConfigObjectOffset(Defined *addrSym, int64_t addrOff,
                                           Defined &object,
                                           int64_t &objectOff) {
  if (!addrSym || !addrSym->section || addrSym->section != object.section)
    return false;
  uint64_t targetOff = 0;
  if (!checkedAddend(addrSym->value, addrOff, targetOff))
    return false;
  uint64_t objectEnd = object.size ? object.value + object.size : object.value + 1;
  if (targetOff < object.value || targetOff >= objectEnd)
    return false;
  objectOff = static_cast<int64_t>(targetOff - object.value);
  return true;
}

static bool resolveRISCVConfigTrackedAddress(
    Defined *addrSym, int64_t addrOff,
    ArrayRef<RISCVConfigTrackedGlobal> globals,
    const RISCVConfigTrackedGlobal *&tracked, int64_t &objectOff) {
  for (const RISCVConfigTrackedGlobal &g : globals) {
    if (!g.sym)
      continue;
    if (resolveRISCVConfigObjectOffset(addrSym, addrOff, *g.sym, objectOff)) {
      tracked = &g;
      return true;
    }
  }
  return false;
}

static bool riscvConfigTrackedGlobalsSafe(
    ArrayRef<RISCVConfigTrackedGlobal> globals) {
  return llvm::all_of(globals, [](const RISCVConfigTrackedGlobal &g) {
    return g.sym && !g.audit.addressTaken && !g.audit.unknownPointerUse &&
           !g.audit.writerFunctions.empty() &&
           g.audit.writerFunctions.count("unresolved-function") == 0 &&
           g.audit.writerFunctions.count("ambiguous-function") == 0;
  });
}

static bool riscvConfigAllTrackedKnown(
    const RISCVConfigEvalState &state,
    ArrayRef<RISCVConfigTrackedGlobal> globals) {
  return llvm::all_of(globals, [&](const RISCVConfigTrackedGlobal &g) {
    auto it = state.trackedGlobals.find(g.sym);
    return it != state.trackedGlobals.end() &&
           it->second.kind == RISCVConfigValueKind::Integer;
  });
}

static bool riscvConfigWriterFunctionsCovered(
    ArrayRef<RISCVConfigTrackedGlobal> globals,
    const std::set<std::string> &evaluatedFunctions) {
  return llvm::all_of(globals, [&](const RISCVConfigTrackedGlobal &g) {
    return llvm::all_of(g.audit.writerFunctions, [&](const std::string &name) {
      return evaluatedFunctions.count(name) != 0;
    });
  });
}

static bool riscvConfigFunctionMayWriteTrackedGlobals(
    Defined *callee, ArrayRef<RISCVConfigTrackedGlobal> globals) {
  if (!callee)
    return true;
  std::string name = callee->getName().str();
  return llvm::any_of(globals, [&](const RISCVConfigTrackedGlobal &g) {
    return g.audit.writerFunctions.count(name) != 0;
  });
}

static void riscvConfigClobberCallerSaved(RISCVConfigEvalState &state) {
  constexpr int regs[] = {1,  5,  6,  7,  10, 11, 12, 13,
                          14, 15, 16, 17, 28, 29, 30, 31};
  for (int r : regs)
    state.regs[r] = {};
  state.regs[0] = riscvConfigInteger(0);
}

static bool isRISCVConfigReturn(const RISCVConfigInsn &insn) {
  if (insn.size == 4 && (insn.raw & 0x7f) == 0x67)
    return insn.rd == 0 && insn.rs1 == 1 && bits(insn.raw, 31, 20) == 0;
  if (insn.size == 2 && (insn.raw & 3) == 2 && bits(insn.raw, 15, 13) == 4)
    return bits(insn.raw, 11, 7) == 1 && bits(insn.raw, 6, 2) == 0;
  return false;
}

static bool evaluateRISCVConfigBranch(uint32_t insn, int64_t lhs, int64_t rhs,
                                      bool &taken) {
  uint32_t funct3 = bits(insn, 14, 12);
  uint32_t lhs32 = static_cast<uint32_t>(lhs);
  uint32_t rhs32 = static_cast<uint32_t>(rhs);
  switch (funct3) {
  case 0:
    taken = lhs32 == rhs32;
    return true;
  case 1:
    taken = lhs32 != rhs32;
    return true;
  case 4:
    taken = static_cast<int32_t>(lhs32) < static_cast<int32_t>(rhs32);
    return true;
  case 5:
    taken = static_cast<int32_t>(lhs32) >= static_cast<int32_t>(rhs32);
    return true;
  case 6:
    taken = lhs32 < rhs32;
    return true;
  case 7:
    taken = lhs32 >= rhs32;
    return true;
  default:
    return false;
  }
}

static int64_t decodeRISCVConfigBImm(uint32_t insn) {
  uint32_t imm = (bits(insn, 31, 31) << 12) |
                 (bits(insn, 7, 7) << 11) |
                 (bits(insn, 30, 25) << 5) |
                 (bits(insn, 11, 8) << 1);
  return SignExtend64<13>(imm);
}

static int64_t decodeRISCVConfigJImm(uint32_t insn) {
  uint32_t imm = (bits(insn, 31, 31) << 20) |
                 (bits(insn, 19, 12) << 12) |
                 (bits(insn, 20, 20) << 11) |
                 (bits(insn, 30, 21) << 1);
  return SignExtend64<21>(imm);
}

struct RISCVConfigBranchTarget {
  bool ok = false;
  uint64_t target = 0;
  StringRef source = "raw";
  std::string reason;
  std::string relocSymbol = "none";
  std::string relocSection = "none";
  int64_t relocAddend = 0;
};

struct RISCVConfigDirectCallTarget {
  bool found = false;
  bool ok = false;
  Defined *target = nullptr;
  bool tail = false;
  uint64_t size = 0;
  std::string reason;
};

static bool
convertRISCVConfigTargetOffset(InputSectionBase &evalSec,
                               InputSectionBase &targetSec,
                               uint64_t targetOff, uint64_t &evalOff) {
  if (&targetSec == &evalSec) {
    evalOff = targetOff;
    return true;
  }

  InputSectionBase *targetParent = &targetSec;
  uint64_t parentOff = targetOff;
  auto targetStorage = riscvFunctionSplitRelocStorage.find(&targetSec);
  if (targetStorage != riscvFunctionSplitRelocStorage.end() &&
      targetStorage->second.parent) {
    targetParent = targetStorage->second.parent;
    if (targetOff > std::numeric_limits<uint64_t>::max() -
                        targetStorage->second.originalBegin)
      return false;
    parentOff = targetStorage->second.originalBegin + targetOff;
  }

  if (&evalSec == targetParent) {
    evalOff = parentOff;
    return true;
  }

  auto evalStorage = riscvFunctionSplitRelocStorage.find(&evalSec);
  if (evalStorage != riscvFunctionSplitRelocStorage.end() &&
      evalStorage->second.parent == targetParent) {
    if (parentOff < evalStorage->second.originalBegin ||
        parentOff >= evalStorage->second.originalEnd)
      return false;
    evalOff = parentOff - evalStorage->second.originalBegin;
    return true;
  }

  return false;
}

static RISCVConfigBranchTarget resolveRISCVConfigBranchTarget(
    InputSectionBase &sec, const RISCVConfigInsn &insn,
    const DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> &relocMap) {
  RISCVConfigBranchTarget result;
  auto it = relocMap.find(insn.off);
  const RISCVConfigRelocInfo *branchReloc = nullptr;
  if (it != relocMap.end()) {
    for (const RISCVConfigRelocInfo &r : it->second) {
      if (r.type != R_RISCV_BRANCH)
        continue;
      if (branchReloc) {
        result.reason = "ambiguous-branch-relocation";
        return result;
      }
      branchReloc = &r;
    }
  }

  if (branchReloc) {
    result.source = "relocation";
    result.relocAddend = branchReloc->addend;
    if (!branchReloc->target) {
      result.reason = "branch-relocation-target-unresolved";
      return result;
    }
    result.relocSymbol = branchReloc->target->getName().str();
    auto *targetSec =
        dyn_cast_or_null<InputSectionBase>(branchReloc->target->section);
    if (!targetSec) {
      result.reason = "branch-relocation-target-section-unresolved";
      return result;
    }
    result.relocSection = targetSec->name.str();
    uint64_t targetOff = 0;
    if (!checkedAddend(branchReloc->target->value, branchReloc->addend,
                       targetOff)) {
      result.reason = "branch-relocation-target-overflow";
      return result;
    }
    if (!convertRISCVConfigTargetOffset(sec, *targetSec, targetOff,
                                        result.target)) {
      result.reason = "branch-relocation-target-out-of-section";
      return result;
    }
    result.ok = true;
    return result;
  }

  int64_t signedTarget =
      static_cast<int64_t>(insn.off) + decodeRISCVConfigBImm(insn.raw);
  if (signedTarget < 0) {
    result.reason = "branch-target-out-of-range";
    return result;
  }
  result.target = static_cast<uint64_t>(signedTarget);
  result.ok = true;
  return result;
}

static RISCVConfigBranchTarget resolveRISCVConfigJalTarget(
    InputSectionBase &sec, const RISCVConfigInsn &insn,
    const DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> &relocMap) {
  RISCVConfigBranchTarget result;
  auto it = relocMap.find(insn.off);
  const RISCVConfigRelocInfo *jalReloc = nullptr;
  if (it != relocMap.end()) {
    for (const RISCVConfigRelocInfo &r : it->second) {
      if (r.type != R_RISCV_JAL)
        continue;
      if (jalReloc) {
        result.reason = "ambiguous-jal-relocation";
        return result;
      }
      jalReloc = &r;
    }
  }
  if (jalReloc) {
    result.source = "relocation";
    result.relocAddend = jalReloc->addend;
    if (!jalReloc->target) {
      result.reason = "jal-relocation-target-unresolved";
      return result;
    }
    result.relocSymbol = jalReloc->target->getName().str();
    auto *targetSec =
        dyn_cast_or_null<InputSectionBase>(jalReloc->target->section);
    if (!targetSec) {
      result.reason = "jal-relocation-target-section-unresolved";
      return result;
    }
    result.relocSection = targetSec->name.str();
    uint64_t targetOff = 0;
    if (!checkedAddend(jalReloc->target->value, jalReloc->addend, targetOff)) {
      result.reason = "jal-relocation-target-overflow";
      return result;
    }
    if (!convertRISCVConfigTargetOffset(sec, *targetSec, targetOff,
                                        result.target)) {
      result.reason = "jal-relocation-target-out-of-section";
      return result;
    }
    result.ok = true;
    return result;
  }
  int64_t signedTarget =
      static_cast<int64_t>(insn.off) + decodeRISCVConfigJImm(insn.raw);
  if (signedTarget < 0) {
    result.reason = "jal-target-out-of-range";
    return result;
  }
  result.target = static_cast<uint64_t>(signedTarget);
  result.ok = true;
  return result;
}

static RISCVConfigBranchTarget resolveRISCVConfigRvcControlTarget(
    InputSectionBase &sec, const RISCVConfigInsn &insn,
    const DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> &relocMap,
    RelType expected) {
  RISCVConfigBranchTarget result;
  auto it = relocMap.find(insn.off);
  const RISCVConfigRelocInfo *reloc = nullptr;
  if (it != relocMap.end()) {
    for (const RISCVConfigRelocInfo &r : it->second) {
      if (r.type != expected)
        continue;
      if (reloc) {
        result.reason = "ambiguous-rvc-control-relocation";
        return result;
      }
      reloc = &r;
    }
  }
  if (!reloc) {
    result.reason = "rvc-control-relocation-missing";
    return result;
  }
  result.source = "relocation";
  result.relocAddend = reloc->addend;
  if (!reloc->target) {
    result.reason = "rvc-control-target-unresolved";
    return result;
  }
  result.relocSymbol = reloc->target->getName().str();
  auto *targetSec = dyn_cast_or_null<InputSectionBase>(reloc->target->section);
  if (!targetSec) {
    result.reason = "rvc-control-target-section-unresolved";
    return result;
  }
  result.relocSection = targetSec->name.str();
  uint64_t targetOff = 0;
  if (!checkedAddend(reloc->target->value, reloc->addend, targetOff)) {
    result.reason = "rvc-control-target-overflow";
    return result;
  }
  if (!convertRISCVConfigTargetOffset(sec, *targetSec, targetOff,
                                      result.target)) {
    result.reason = "rvc-control-target-out-of-section";
    return result;
  }
  result.ok = true;
  return result;
}

static RISCVConfigDirectCallTarget resolveRISCVConfigDirectCallTarget(
    InputSectionBase &sec, const RISCVConfigInsn &insn,
    const DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> &relocMap) {
  RISCVConfigDirectCallTarget result;
  auto it = relocMap.find(insn.off);
  const RISCVConfigRelocInfo *callReloc = nullptr;
  if (it != relocMap.end()) {
    for (const RISCVConfigRelocInfo &r : it->second) {
      if (!isRISCVConfigDirectCallRel(r.type))
        continue;
      if (callReloc) {
        result.found = true;
        result.reason = "ambiguous-direct-call-relocation";
        return result;
      }
      callReloc = &r;
    }
  }
  if (!callReloc)
    return result;
  result.found = true;
  result.target = callReloc->target;
  if (callReloc->type == R_RISCV_JAL && insn.size == 4 &&
      (insn.raw & 0x7f) == 0x6f && insn.rd == 0 &&
      (!result.target || result.target->type != STT_FUNC)) {
    result.found = false;
    return result;
  }
  if (!result.target || result.target->type != STT_FUNC) {
    result.reason = "direct-call-target-not-function";
    return result;
  }
  if (callReloc->type == R_RISCV_CALL || callReloc->type == R_RISCV_CALL_PLT) {
    ArrayRef<uint8_t> data = sec.content();
    if (insn.off + 8 > data.size()) {
      result.reason = "direct-call-pair-out-of-section";
      return result;
    }
    uint32_t jalr = llvm::support::endian::read32le(data.data() + insn.off + 4);
    if ((jalr & 0x7f) != 0x67) {
      result.reason = "direct-call-pair-not-jalr";
      return result;
    }
    uint32_t rd = bits(jalr, 11, 7);
    if (rd == 0)
      result.tail = true;
    else if (rd == 1 || rd == 5)
      result.tail = false;
    else {
      result.reason = "direct-call-link-register-unsupported";
      return result;
    }
    result.size = 8;
    result.ok = true;
    return result;
  }
  if (callReloc->type == R_RISCV_JAL) {
    if (insn.size != 4 || (insn.raw & 0x7f) != 0x6f) {
      result.reason = "jal-call-relocation-not-jal";
      return result;
    }
    if (insn.rd == 0)
      result.tail = true;
    else if (insn.rd == 1 || insn.rd == 5)
      result.tail = false;
    else {
      result.reason = "jal-call-link-register-unsupported";
      return result;
    }
    result.size = 4;
    result.ok = true;
    return result;
  }
  result.reason = "unsupported-direct-call-relocation";
  return result;
}

static bool riscvConfigValueTargetsObject(const RISCVConfigValue &addr,
                                          Defined *&sym, int64_t &offset) {
  if (addr.kind != RISCVConfigValueKind::SymbolAddress || !addr.symbol)
    return false;
  sym = addr.symbol;
  offset = addr.offset;
  return true;
}

template <class ELFT>
static SmallVector<RISCVConfigBasicBlock, 0>
buildRISCVConfigCFG(InputSectionBase &sec, Defined &func,
                    std::string &reason) {
  ArrayRef<uint8_t> data = sec.content();
  DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> relocMap =
      getRISCVConfigRelocs<ELFT>(sec);
  DenseSet<uint64_t> boundaries;
  boundaries.insert(func.value);
  SmallVector<RISCVConfigInsn, 0> allInsns;
  for (uint64_t off = func.value; off < func.value + func.size;) {
    RISCVConfigInsn insn = decodeRISCVConfigInsn(data, off);
    if (insn.size == 0 || off + insn.size > func.value + func.size) {
      reason = "decode-failed";
      return {};
    }
    allInsns.push_back(insn);
    if (insn.size == 4 && (insn.raw & 0x7f) == 0x63) {
      RISCVConfigBranchTarget target =
          resolveRISCVConfigBranchTarget(sec, insn, relocMap);
      if (!target.ok) {
        reason = target.reason;
        return {};
      }
      uint64_t fallthrough = off + insn.size;
      if (target.target >= func.value && target.target < func.value + func.size)
        boundaries.insert(target.target);
      if (fallthrough < func.value + func.size)
        boundaries.insert(fallthrough);
    }
    if (insn.size == 4 && (insn.raw & 0x7f) == 0x6f) {
      RISCVConfigBranchTarget target =
          resolveRISCVConfigJalTarget(sec, insn, relocMap);
      if (!target.ok) {
        reason = target.reason;
        return {};
      }
      uint64_t fallthrough = off + insn.size;
      if (target.target >= func.value && target.target < func.value + func.size)
        boundaries.insert(target.target);
      if (fallthrough < func.value + func.size)
        boundaries.insert(fallthrough);
    }
    off += insn.size;
  }

  RelsOrRelas<ELFT> rels = sec.template relsOrRelas<ELFT>();
  auto scan = [&](auto relRange) {
    for (const auto &rel : relRange) {
      uint64_t off = rel.r_offset;
      if (off < func.value || off >= func.value + func.size)
        continue;
      RelType type = rel.getType(config->isMips64EL);
      if (type != R_RISCV_BRANCH && type != R_RISCV_JAL &&
          type != R_RISCV_RVC_BRANCH && type != R_RISCV_RVC_JUMP)
        continue;
      Defined *target = getRISCVConfigRelocTarget<ELFT>(sec, rel);
      if (!target || target->section != &sec)
        continue;
      uint64_t targetOff = 0;
      if (checkedAddend(target->value, getRISCVFunctionSplitAddend(rel),
                        targetOff) &&
          targetOff >= func.value && targetOff < func.value + func.size)
        boundaries.insert(targetOff);
      auto it = llvm::find_if(allInsns, [&](const RISCVConfigInsn &insn) {
        return insn.off == off;
      });
      if (it != allInsns.end()) {
        uint64_t next = it->off + it->size;
        if (next < func.value + func.size)
          boundaries.insert(next);
      }
    }
  };
  scan(rels.rels);
  scan(rels.relas);

  SmallVector<uint64_t, 0> sorted;
  for (uint64_t off : boundaries)
    sorted.push_back(off);
  llvm::sort(sorted);
  SmallVector<RISCVConfigBasicBlock, 0> blocks;
  for (auto [i, begin] : llvm::enumerate(sorted)) {
    uint64_t end =
        i + 1 == sorted.size() ? func.value + func.size : sorted[i + 1];
    RISCVConfigBasicBlock block;
    block.begin = begin;
    block.end = end;
    for (const RISCVConfigInsn &insn : allInsns)
      if (insn.off >= begin && insn.off < end)
        block.insns.push_back(insn);
    if (!block.insns.empty())
      blocks.push_back(std::move(block));
  }
  return blocks;
}

template <class ELFT>
static RISCVConfigProofResult
tryEvaluateRISCVConfigInitialization(
    ArrayRef<RISCVConfigCallRecord> calls,
    ArrayRef<RISCVConfigTrackedGlobal> trackedGlobals) {
  RISCVConfigProofResult result;
  for (const RISCVConfigTrackedGlobal &g : trackedGlobals)
    result.values[g.name] = std::nullopt;

  if (calls.empty()) {
    result.reason = "no-entry-call";
    return result;
  }
  if (!riscvConfigTrackedGlobalsSafe(trackedGlobals)) {
    result.reason = "tracked-global-safety-not-proven";
    return result;
  }
  if (llvm::any_of(calls, [](const RISCVConfigCallRecord &rec) {
        return !rec.arg0Proven || !rec.arg1Proven;
      })) {
    result.reason = "non-constant-entry-args";
    return result;
  }
  std::set<std::pair<int64_t, int64_t>> argSets;
  for (const RISCVConfigCallRecord &rec : calls)
    argSets.insert({rec.arg0Value, rec.arg1Value});
  if (argSets.size() != 1) {
    result.reason = "multiple-entry-arg-sets";
    return result;
  }

  bool ambiguous = false;
  Defined *entry = findUniqueRISCVConfigDefinedByName<ELFT>(
      "initeccsize", STT_FUNC, ambiguous);
  if (!entry) {
    result.reason = ambiguous ? "ambiguous-entry-symbol" : "entry-not-found";
    return result;
  }
  struct Frame {
    Defined *func = nullptr;
    InputSectionBase *sec = nullptr;
    SmallVector<RISCVConfigBasicBlock, 0> blocks;
    DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> relocMap;
    DenseSet<uint64_t> blockBoundaries;
    DenseSet<uint64_t> visited;
    uint64_t current = 0;
    uint64_t skipUntil = 0;
  };

  auto buildFrame = [&](Defined *func, Frame &frame,
                        std::string &reason) -> bool {
    if (!func || !func->section || !isa<InputSectionBase>(func->section)) {
      reason = "function-section-not-input";
      return false;
    }
    frame = {};
    frame.func = func;
    frame.sec = cast<InputSectionBase>(func->section);
    frame.blocks = buildRISCVConfigCFG<ELFT>(*frame.sec, *func, reason);
    if (frame.blocks.empty()) {
      if (reason.empty())
        reason = "empty-cfg";
      return false;
    }
    frame.relocMap = getRISCVConfigRelocs<ELFT>(*frame.sec);
    for (const RISCVConfigBasicBlock &block : frame.blocks)
      frame.blockBoundaries.insert(block.begin);
    frame.current = func->value;
    return true;
  };

  RISCVConfigEvalState state;
  for (auto &r : state.regs)
    r = {};
  state.regs[0] = riscvConfigInteger(0);
  state.regs[2] = riscvConfigStackAddress(0);
  auto [arg0, arg1] = *argSets.begin();
  state.regs[10] = riscvConfigInteger(arg0);
  state.regs[11] = riscvConfigInteger(arg1);
  for (const RISCVConfigTrackedGlobal &g : trackedGlobals)
    state.trackedGlobals[g.sym] = {};

  std::set<std::string> evaluatedFunctions;

  auto hasRemainingTrackedStore = [&](const Frame &f, uint64_t after) {
    for (const auto &kv : f.relocMap) {
      uint64_t off = kv.first;
      if (off <= after || off < f.func->value || off >= f.func->value + f.func->size)
        continue;
      const RISCVConfigRelocInfo *lo =
          findRISCVConfigReloc(kv.second, {R_RISCV_LO12_S});
      if (lo && lo->target) {
        const RISCVConfigTrackedGlobal *tracked = nullptr;
        int64_t trackedOff = 0;
        if (resolveRISCVConfigTrackedAddress(lo->target, lo->addend,
                                             trackedGlobals, tracked,
                                             trackedOff))
          return true;
      }
    }
    return false;
  };

  auto proofCanStop = [&](const Frame &f, uint64_t after) {
    return riscvConfigAllTrackedKnown(state, trackedGlobals) &&
           riscvConfigWriterFunctionsCovered(trackedGlobals,
                                             evaluatedFunctions) &&
           !hasRemainingTrackedStore(f, after);
  };
  Frame frame;
  std::string cfgReason;
  if (!buildFrame(entry, frame, cfgReason)) {
    result.reason = cfgReason;
    result.failFunction = entry->getName().str();
    return result;
  }
  ++result.functionsEvaluated;
  evaluatedFunctions.insert(entry->getName().str());
  result.evaluatedFunctionNames.insert(entry->getName().str());

  for (uint32_t steps = 0; steps < 4096;) {
    auto blockIt = llvm::find_if(frame.blocks, [&](const RISCVConfigBasicBlock &b) {
      return b.begin == frame.current;
    });
    if (blockIt == frame.blocks.end()) {
      result.reason = "missing-basic-block";
      result.failFunction = frame.func->getName().str();
      result.failOffset = frame.current;
      return result;
    }
    if (!frame.visited.insert(frame.current).second)
      ++result.loopIterations;
    ++result.visitedBlocks;
    const RISCVConfigBasicBlock &block = *blockIt;
    bool transferred = false;
    for (const RISCVConfigInsn &insn : block.insns) {
      if (insn.off < frame.skipUntil) {
        if (insn.off + insn.size >= frame.skipUntil)
          frame.skipUntil = 0;
        continue;
      }
      ++steps;
      ++result.executedInstructions;
      result.failOffset = insn.off;
      result.failOpcode = insn.raw & 0x7f;
      result.failFunction = frame.func->getName().str();
      result.failKind = insn.kind;
      if (insn.size == 2) {
        result.failRaw16 = static_cast<uint16_t>(insn.raw);
        result.failQuadrant = insn.raw & 3;
        result.failFunct3 = bits(insn.raw, 15, 13);
        result.failBit12 = bits(insn.raw, 12, 12);
        result.failRd = insn.rd;
        result.failRs2 = insn.rs2;
      } else {
        result.failRaw16 = 0;
        result.failQuadrant = 0;
        result.failFunct3 = 0;
        result.failBit12 = 0;
        result.failRd = insn.rd;
        result.failRs2 = insn.rs2;
      }
      if (steps >= 4096) {
        result.reason = "evaluator-step-limit";
        return result;
      }
      state.regs[0] = riscvConfigInteger(0);
      RISCVConfigDirectCallTarget directCall =
          resolveRISCVConfigDirectCallTarget(*frame.sec, insn, frame.relocMap);
      if (directCall.found) {
        if (!directCall.ok) {
          result.reason = directCall.reason;
          return result;
        }
        ++result.directCalls;
        message(Twine("riscv-config-call: caller=") +
                frame.func->getName() +
                " callee=" + directCall.target->getName() +
                " kind=" + (directCall.tail ? Twine("tail") : Twine("regular")) +
                " action=" +
                (directCall.tail ? Twine("enter") : Twine("abstract")) +
                " args_known=" +
                Twine((state.regs[10].kind == RISCVConfigValueKind::Integer &&
                       state.regs[11].kind == RISCVConfigValueKind::Integer)
                          ? 1
                          : 0));
        if (directCall.tail) {
          std::array<RISCVConfigValue, 32> oldRegs = state.regs;
          for (auto &r : state.regs)
            r = {};
          state.regs[0] = riscvConfigInteger(0);
          state.regs[2] = oldRegs[2];
          for (int r = 10; r <= 17; ++r)
            state.regs[r] = oldRegs[r];
          std::string callReason;
          if (!buildFrame(directCall.target, frame, callReason)) {
            result.reason = callReason;
            result.failFunction = directCall.target->getName().str();
            return result;
          }
          ++result.functionsEvaluated;
          evaluatedFunctions.insert(directCall.target->getName().str());
          result.evaluatedFunctionNames.insert(directCall.target->getName().str());
          transferred = true;
          break;
        }
        if (riscvConfigFunctionMayWriteTrackedGlobals(directCall.target,
                                                      trackedGlobals)) {
          result.reason = "abstract-call-may-write-tracked-global";
          return result;
        }
        if (!riscvConfigTrackedGlobalsSafe(trackedGlobals)) {
          result.reason = "abstract-call-global-safety-not-proven";
          return result;
        }
        ++result.abstractCalls;
        riscvConfigClobberCallerSaved(state);
        frame.skipUntil = insn.off + directCall.size;
        continue;
      }
      uint32_t opcode = insn.raw & 0x7f;
      if (insn.size == 2) {
        if (insn.kind == RISCVConfigInsnKind::CLi && insn.rd > 0) {
          state.regs[insn.rd] = riscvConfigInteger(insn.imm);
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CLui && insn.rd > 0) {
          state.regs[insn.rd] = riscvConfigInteger(insn.imm);
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CAddi && insn.rd > 0 &&
            state.regs[insn.rd].kind != RISCVConfigValueKind::Unknown) {
          RISCVConfigValue imm = riscvConfigInteger(insn.imm);
          RISCVConfigValue out;
          if (!riscvConfigAddValues(state.regs[insn.rd], imm, out)) {
            result.reason = "unsupported-c-addi-address-arithmetic";
            return result;
          }
          state.regs[insn.rd] = out;
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CMv && insn.rd > 0) {
          if (state.regs[insn.rs2].kind == RISCVConfigValueKind::Unknown) {
            result.reason = "unknown-c-mv-source";
            return result;
          }
          state.regs[insn.rd] = state.regs[insn.rs2];
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CAdd && insn.rd > 0) {
          if (state.regs[insn.rd].kind == RISCVConfigValueKind::Unknown ||
              state.regs[insn.rs2].kind == RISCVConfigValueKind::Unknown) {
            result.reason = "unknown-c-add-source";
            return result;
          }
          RISCVConfigValue out;
          if (!riscvConfigAddValues(state.regs[insn.rd], state.regs[insn.rs2],
                                    out)) {
            result.reason = "unsupported-c-add-address-arithmetic";
            return result;
          }
          state.regs[insn.rd] = out;
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CSlli && insn.rd > 0) {
          if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer) {
            result.reason = "unknown-c-slli-source";
            return result;
          }
          state.regs[insn.rd] = riscvConfigInteger(
              static_cast<uint32_t>(state.regs[insn.rs1].value) << insn.imm);
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CSrli ||
            insn.kind == RISCVConfigInsnKind::CSrai ||
            insn.kind == RISCVConfigInsnKind::CAndi) {
          if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer) {
            result.reason = "unknown-c-misc-alu-source";
            return result;
          }
          uint32_t src = static_cast<uint32_t>(state.regs[insn.rs1].value);
          if (insn.kind == RISCVConfigInsnKind::CSrli)
            state.regs[insn.rd] = riscvConfigInteger(src >> insn.imm);
          else if (insn.kind == RISCVConfigInsnKind::CSrai)
            state.regs[insn.rd] = riscvConfigInteger(
                static_cast<int32_t>(src) >> insn.imm);
          else
            state.regs[insn.rd] = riscvConfigInteger(
                src & static_cast<uint32_t>(insn.imm));
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CSub ||
            insn.kind == RISCVConfigInsnKind::CXor ||
            insn.kind == RISCVConfigInsnKind::COr ||
            insn.kind == RISCVConfigInsnKind::CAnd) {
          if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer ||
              state.regs[insn.rs2].kind != RISCVConfigValueKind::Integer) {
            result.reason = "unknown-c-reg-alu-source";
            return result;
          }
          uint32_t lhs = static_cast<uint32_t>(state.regs[insn.rs1].value);
          uint32_t rhs = static_cast<uint32_t>(state.regs[insn.rs2].value);
          uint32_t out = 0;
          if (insn.kind == RISCVConfigInsnKind::CSub)
            out = lhs - rhs;
          else if (insn.kind == RISCVConfigInsnKind::CXor)
            out = lhs ^ rhs;
          else if (insn.kind == RISCVConfigInsnKind::COr)
            out = lhs | rhs;
          else
            out = lhs & rhs;
          state.regs[insn.rd] = riscvConfigInteger(out);
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CSwsp) {
          if (state.regs[2].kind != RISCVConfigValueKind::StackAddress) {
            result.reason = "c-swsp-sp-not-stack";
            return result;
          }
          state.stackSlots[state.regs[2].offset + insn.imm] =
              state.regs[insn.rs2];
          message(Twine("riscv-config-store: function=") +
                  frame.func->getName() +
                  " offset=0x" + Twine::utohexstr(insn.off) +
                  " target=stack" +
                  " value=" +
                  (state.regs[insn.rs2].kind == RISCVConfigValueKind::Integer
                       ? Twine(state.regs[insn.rs2].value)
                       : Twine("unknown")) +
                  " target_source=symbolic tracked=0");
          continue;
        }
        if (insn.kind == RISCVConfigInsnKind::CLwsp && insn.rd > 0) {
          if (state.regs[2].kind != RISCVConfigValueKind::StackAddress) {
            result.reason = "c-lwsp-sp-not-stack";
            return result;
          }
          auto slot = state.stackSlots.find(state.regs[2].offset + insn.imm);
          state.regs[insn.rd] =
              slot == state.stackSlots.end() ? RISCVConfigValue{} : slot->second;
          continue;
        }
        if (isRISCVConfigReturn(insn)) {
          if (proofCanStop(frame, insn.off)) {
            result.complete = true;
            result.reason = "complete";
            return result;
          }
          result.reason = "return-before-complete";
          return result;
        }
        result.reason = "unsupported-compressed-instruction";
        return result;
      }
      if (opcode == 0x13 && insn.rd > 0) {
        uint32_t funct3 = bits(insn.raw, 14, 12);
        if (state.regs[insn.rs1].kind == RISCVConfigValueKind::Unknown) {
          result.reason = "unknown-op-imm-source";
          return result;
        }
        if (funct3 == 0) {
          RISCVConfigValue out;
          if (!riscvConfigAddValues(state.regs[insn.rs1],
                                    riscvConfigInteger(insn.imm), out)) {
            result.reason = "unsupported-addi-address-arithmetic";
            return result;
          }
          auto it = frame.relocMap.find(insn.off);
          if (it != frame.relocMap.end()) {
            const RISCVConfigRelocInfo *lo = findRISCVConfigReloc(
                it->second, {R_RISCV_LO12_I, R_RISCV_PCREL_LO12_I});
            if (lo && lo->target)
              out = riscvConfigSymbolAddress(lo->target, lo->addend);
          }
          state.regs[insn.rd] = out;
        } else if (funct3 == 7 &&
                   state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer) {
          state.regs[insn.rd] =
              riscvConfigInteger(static_cast<uint32_t>(
                  state.regs[insn.rs1].value) &
                                 static_cast<uint32_t>(insn.imm));
        } else if (funct3 == 1 && bits(insn.raw, 31, 25) == 0 &&
                   state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer) {
          state.regs[insn.rd] = riscvConfigInteger(static_cast<uint32_t>(
              state.regs[insn.rs1].value) << bits(insn.raw, 24, 20));
        } else if (funct3 == 5 && bits(insn.raw, 31, 25) == 0 &&
                   state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer) {
          state.regs[insn.rd] = riscvConfigInteger(
              static_cast<uint32_t>(state.regs[insn.rs1].value) >>
              bits(insn.raw, 24, 20));
        } else {
          result.reason = "unsupported-op-imm";
          return result;
        }
        continue;
      }
      if ((opcode == 0x37 || opcode == 0x17) && insn.rd > 0) {
        auto it = frame.relocMap.find(insn.off);
        if (it != frame.relocMap.end()) {
          const RISCVConfigRelocInfo *hi =
              findRISCVConfigReloc(it->second, {R_RISCV_HI20, R_RISCV_PCREL_HI20});
          if (hi && hi->target) {
            state.regs[insn.rd] = riscvConfigSymbolAddress(hi->target,
                                                            hi->addend);
            continue;
          }
          result.reason = "symbolic-address-reloc-unresolved";
          return result;
        }
        state.regs[insn.rd] = riscvConfigInteger(insn.imm);
        continue;
      }
      if (opcode == 0x33) {
        uint32_t funct3 = bits(insn.raw, 14, 12);
        uint32_t funct7 = bits(insn.raw, 31, 25);
        if (state.regs[insn.rs1].kind == RISCVConfigValueKind::Unknown ||
            state.regs[insn.rs2].kind == RISCVConfigValueKind::Unknown) {
          result.reason = "unknown-op-source";
          return result;
        }
        if (funct3 == 0 && funct7 == 0) {
          if (state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer &&
              state.regs[insn.rs2].kind == RISCVConfigValueKind::Integer) {
            state.regs[insn.rd] = riscvConfigInteger(
                static_cast<uint32_t>(state.regs[insn.rs1].value) +
                static_cast<uint32_t>(state.regs[insn.rs2].value));
          } else {
            RISCVConfigValue out;
            if (!riscvConfigAddValues(state.regs[insn.rs1],
                                      state.regs[insn.rs2], out)) {
              result.reason = "unsupported-add-address-arithmetic";
              return result;
            }
            state.regs[insn.rd] = out;
          }
        } else if (funct3 == 0 && funct7 == 0x20 &&
                   state.regs[insn.rs2].kind == RISCVConfigValueKind::Integer) {
          if (state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer) {
            state.regs[insn.rd] = riscvConfigInteger(
                static_cast<uint32_t>(state.regs[insn.rs1].value) -
                static_cast<uint32_t>(state.regs[insn.rs2].value));
          } else {
            RISCVConfigValue out;
            if (!riscvConfigSubInteger(state.regs[insn.rs1],
                                       state.regs[insn.rs2].value, out)) {
              result.reason = "unsupported-sub-address-arithmetic";
              return result;
            }
            state.regs[insn.rd] = out;
          }
        } else if (funct3 == 0 && funct7 == 1 &&
                   state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer &&
                   state.regs[insn.rs2].kind == RISCVConfigValueKind::Integer)
          state.regs[insn.rd] = riscvConfigInteger(
              static_cast<uint32_t>(
                  static_cast<uint64_t>(static_cast<uint32_t>(
                      state.regs[insn.rs1].value)) *
                  static_cast<uint64_t>(static_cast<uint32_t>(
                      state.regs[insn.rs2].value))));
        else {
          result.reason = "unsupported-op";
          return result;
        }
        continue;
      }
      if (opcode == 0x03) {
        uint32_t loadKind = bits(insn.raw, 14, 12);
        if (loadKind != 2 && loadKind != 4) {
          result.reason = "unsupported-load-kind";
          return result;
        }
        RISCVConfigValue base = state.regs[insn.rs1];
        if (base.kind == RISCVConfigValueKind::StackAddress) {
          auto slot = state.stackSlots.find(base.offset + insn.imm);
          if (slot == state.stackSlots.end()) {
            state.regs[insn.rd] = {};
            continue;
          }
          state.regs[insn.rd] = slot->second;
          continue;
        }
        if (loadKind != 4) {
          result.reason = "non-byte-load-from-non-stack";
          return result;
        }
        if (base.kind != RISCVConfigValueKind::SymbolAddress) {
          result.reason = "readonly-load-base-not-symbol";
          return result;
        }
        Defined *loadSym = base.symbol;
        int64_t loadOff = base.offset + insn.imm;
        const RISCVConfigTrackedGlobal *trackedLoad = nullptr;
        int64_t trackedLoadOff = 0;
        if (resolveRISCVConfigTrackedAddress(loadSym, loadOff, trackedGlobals,
                                             trackedLoad, trackedLoadOff)) {
          auto val = state.trackedGlobals.find(trackedLoad->sym);
          if (val == state.trackedGlobals.end() ||
              val->second.kind != RISCVConfigValueKind::Integer) {
            result.reason = "tracked-global-load-unknown";
            return result;
          }
          if (trackedLoadOff != 0) {
            result.reason = "tracked-global-load-offset";
            return result;
          }
          state.regs[insn.rd] = val->second;
          continue;
        }
        uint8_t byte = 0;
        std::string loadReason;
        if (!readRISCVConfigReadonlyByte(loadSym, loadOff, byte, loadReason)) {
          result.reason = loadReason;
          return result;
        }
        result.readonlySourceObjects.insert(loadSym);
        state.regs[insn.rd] = riscvConfigInteger(byte);
        ++result.readonlyLoads;
        continue;
      }
      if (opcode == 0x23) {
        uint32_t funct3 = bits(insn.raw, 14, 12);
        if (funct3 != 0 && funct3 != 2) {
          result.reason = "unsupported-store-kind";
          return result;
        }
        RISCVConfigValue storeValue = state.regs[insn.rs2];
        RISCVConfigValue addr = state.regs[insn.rs1];
        std::string targetSource = "symbolic";
        auto it = frame.relocMap.find(insn.off);
        if (it != frame.relocMap.end()) {
          const RISCVConfigRelocInfo *lo =
              findRISCVConfigReloc(it->second, {R_RISCV_LO12_S});
          if (lo && lo->target) {
            addr = riscvConfigSymbolAddress(lo->target, lo->addend);
            targetSource = "relocation";
          } else {
            result.reason = "store-relocation-unresolved";
            return result;
          }
        } else {
          RISCVConfigValue out;
          if (!riscvConfigAddValues(addr, riscvConfigInteger(insn.imm), out)) {
            result.reason = "unknown-store-target";
            return result;
          }
          addr = out;
        }

        if (addr.kind == RISCVConfigValueKind::StackAddress) {
          state.stackSlots[addr.offset] = storeValue;
          message(Twine("riscv-config-store: function=") +
                  frame.func->getName() +
                  " offset=0x" + Twine::utohexstr(insn.off) +
                  " target=stack" +
                  " value=" +
                  (storeValue.kind == RISCVConfigValueKind::Integer
                       ? Twine(storeValue.value)
                       : Twine("unknown")) +
                  " target_source=" + targetSource +
                  " tracked=0");
          continue;
        }

        Defined *storeSym = nullptr;
        int64_t storeOff = 0;
        if (!riscvConfigValueTargetsObject(addr, storeSym, storeOff)) {
          result.reason = "unknown-store-target";
          return result;
        }
        const RISCVConfigTrackedGlobal *tracked = nullptr;
        int64_t trackedOff = 0;
        bool isTracked = resolveRISCVConfigTrackedAddress(
            storeSym, storeOff, trackedGlobals, tracked, trackedOff);
        if (isTracked) {
          if (trackedOff != 0) {
            result.reason = "tracked-store-offset";
            return result;
          }
          if (storeValue.kind != RISCVConfigValueKind::Integer) {
            result.reason = "tracked-store-value-unknown";
            return result;
          }
          int64_t byteValue = static_cast<uint8_t>(storeValue.value);
          state.trackedGlobals[tracked->sym] = riscvConfigInteger(byteValue);
          result.values[tracked->name] = byteValue;
          ++result.trackedStores;
        }
        if (!isTracked && (!storeSym || storeSym->type != STT_OBJECT)) {
          result.reason = "non-object-store-target";
          return result;
        }
        message(Twine("riscv-config-store: function=") +
                frame.func->getName() +
                " offset=0x" + Twine::utohexstr(insn.off) +
                " target=" +
                (storeSym ? Twine(storeSym->getName()) : Twine("unknown")) +
                " value=" +
                (storeValue.kind == RISCVConfigValueKind::Integer
                     ? Twine(unsigned(static_cast<uint8_t>(storeValue.value)))
                     : Twine("unknown")) +
                " target_source=" + targetSource +
                " tracked=" + Twine(isTracked ? 1 : 0));
        if (!isTracked && !riscvConfigTrackedGlobalsSafe(trackedGlobals)) {
          result.reason = "unrelated-store-global-safety-not-proven";
          return result;
        }
        continue;
      }
      if (opcode == 0x63) {
        if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer ||
            state.regs[insn.rs2].kind != RISCVConfigValueKind::Integer) {
          result.reason = "unknown-branch-operands";
          return result;
        }
        bool taken = false;
        if (!evaluateRISCVConfigBranch(insn.raw, state.regs[insn.rs1].value,
                                       state.regs[insn.rs2].value, taken)) {
          result.reason = "unsupported-branch-kind";
          return result;
        }
        ++result.constantBranches;
        if (taken)
          ++result.alwaysTakenBranches;
        else
          ++result.neverTakenBranches;
        RISCVConfigBranchTarget branchTarget =
            resolveRISCVConfigBranchTarget(*frame.sec, insn, frame.relocMap);
        if (!branchTarget.ok) {
          result.reason = branchTarget.reason;
          return result;
        }
        int64_t branchImm = decodeRISCVConfigBImm(insn.raw);
        uint64_t takenTarget = branchTarget.target;
        uint64_t fallthrough = insn.off + insn.size;
        uint64_t successor = taken ? takenTarget : fallthrough;
        if (result.branchTraceEmitted < 48) {
          ++result.branchTraceEmitted;
          message(Twine("riscv-config-branch-trace: function=") +
                  frame.func->getName() +
                  " offset=0x" + Twine::utohexstr(insn.off) +
                  " raw=0x" + Twine::utohexstr(insn.raw) +
                  " funct3=" + Twine(bits(insn.raw, 14, 12)) +
                  " lhs=" + Twine(state.regs[insn.rs1].value) +
                  " rhs=" + Twine(state.regs[insn.rs2].value) +
                  " taken=" + Twine(taken ? 1 : 0) +
                  " decoded_imm=" + Twine(branchImm) +
                  " target_source=" + branchTarget.source +
                  " reloc_target_symbol=" + branchTarget.relocSymbol +
                  " reloc_target_section=" + branchTarget.relocSection +
                  " reloc_addend=" + Twine(branchTarget.relocAddend) +
                  " resolved_target=0x" +
                  Twine::utohexstr(branchTarget.target) +
                  " taken_target=0x" + Twine::utohexstr(takenTarget) +
                  " fallthrough=0x" + Twine::utohexstr(fallthrough) +
                  " current_block=0x" + Twine::utohexstr(block.begin));
        }
        if (successor < frame.func->value ||
            successor >= frame.func->value + frame.func->size) {
          result.reason = "branch-target-out-of-function";
          return result;
        }
        if (!frame.blockBoundaries.contains(successor)) {
          result.reason = "branch-target-not-basic-block";
          result.failOffset = successor;
          return result;
        }
        frame.current = successor;
        transferred = true;
        break;
      }
      if (isRISCVConfigReturn(insn)) {
        if (proofCanStop(frame, insn.off)) {
          result.complete = true;
          result.reason = "complete";
          return result;
        }
        result.reason = "return-before-complete";
        return result;
      }
      if (opcode == 0x6f || opcode == 0x67) {
        if (opcode == 0x6f && insn.rd == 0) {
          RISCVConfigBranchTarget jalTarget =
              resolveRISCVConfigJalTarget(*frame.sec, insn, frame.relocMap);
          if (!jalTarget.ok) {
            result.reason = jalTarget.reason;
            return result;
          }
          uint64_t target = jalTarget.target;
          if (target < frame.func->value ||
              target >= frame.func->value + frame.func->size) {
            result.reason = "jal-target-out-of-function";
            return result;
          }
          if (!frame.blockBoundaries.contains(target)) {
            result.reason = "jal-target-not-basic-block";
            result.failOffset = target;
            return result;
          }
          frame.current = target;
          transferred = true;
          break;
        }
        ++result.directCalls;
        result.reason = "interprocedural-evaluator-not-implemented";
        return result;
      }
      result.reason = "unsupported-instruction";
      return result;
    }
    if (!transferred) {
      uint64_t next = block.end;
      if (next >= frame.func->value + frame.func->size) {
        if (proofCanStop(frame, block.end)) {
          result.complete = true;
          result.reason = "complete";
          return result;
        }
        result.reason = "fallthrough-out-of-function-before-complete";
        return result;
      }
      frame.current = next;
    }
    if (proofCanStop(frame, block.end)) {
      result.complete = true;
      result.reason = "complete";
      return result;
    }
  }
  result.reason = "evaluator-step-limit";
  return result;
}

struct RISCVConfigUseAuditResult {
  uint32_t provenConstantGlobals = 0;
  uint32_t constantLoads = 0;
  uint32_t constantBranches = 0;
  uint32_t specializationDependentBranches = 0;
  uint32_t alwaysTakenBranches = 0;
  uint32_t neverTakenBranches = 0;
  uint32_t functionsAnalyzed = 0;
  uint32_t cfgSafeFunctions = 0;
  uint32_t candidateDeadRegions = 0;
  uint32_t safeDeadRegions = 0;
  uint64_t potentialDeadTextBytes = 0;
  uint64_t conservativeDeadTextBytes = 0;
  uint64_t potentialDeadRodataBytes = 0;
  uint64_t conservativeDeadRodataBytes = 0;
  uint64_t candidateInitializationRodataBytes = 0;
  bool initializationOrderProven = false;
  uint32_t unsafeOrUnknownReadSites = 0;
};

struct RISCVConfigDataflowState {
  std::array<RISCVConfigValue, 32> regs;
  bool valid = false;
};

static bool sameRISCVConfigValue(const RISCVConfigValue &a,
                                 const RISCVConfigValue &b) {
  if (a.kind != b.kind)
    return false;
  if (a.kind == RISCVConfigValueKind::Unknown)
    return true;
  if (a.kind == RISCVConfigValueKind::Integer)
    return static_cast<uint32_t>(a.value) == static_cast<uint32_t>(b.value);
  return a.symbol == b.symbol && a.offset == b.offset;
}

static RISCVConfigValue mergeRISCVConfigValue(const RISCVConfigValue &a,
                                              const RISCVConfigValue &b) {
  return sameRISCVConfigValue(a, b) ? a : RISCVConfigValue{};
}

static bool mergeRISCVConfigState(RISCVConfigDataflowState &dst,
                                  const RISCVConfigDataflowState &src) {
  if (!dst.valid) {
    dst = src;
    dst.valid = true;
    return true;
  }
  bool changed = false;
  for (int i = 0; i < 32; ++i) {
    RISCVConfigValue merged = mergeRISCVConfigValue(dst.regs[i], src.regs[i]);
    if (!sameRISCVConfigValue(merged, dst.regs[i])) {
      dst.regs[i] = merged;
      changed = true;
    }
  }
  return changed;
}

static bool evalRISCVConfigIntegerInsn(const RISCVConfigInsn &insn,
                                       RISCVConfigDataflowState &state,
                                       std::string &reason) {
  if (insn.size == 2) {
    if (insn.kind == RISCVConfigInsnKind::CAddi && insn.rd == 0)
      return true;
    if (insn.kind == RISCVConfigInsnKind::CLi && insn.rd > 0) {
      state.regs[insn.rd] = riscvConfigInteger(insn.imm);
      return true;
    }
    if (insn.kind == RISCVConfigInsnKind::CLui && insn.rd > 0) {
      state.regs[insn.rd] = riscvConfigInteger(insn.imm);
      return true;
    }
    if (insn.kind == RISCVConfigInsnKind::CAddi && insn.rd > 0) {
      if (state.regs[insn.rd].kind == RISCVConfigValueKind::Unknown)
        return true;
      RISCVConfigValue out;
      if (!riscvConfigAddValues(state.regs[insn.rd],
                                riscvConfigInteger(insn.imm), out)) {
        state.regs[insn.rd] = {};
        return true;
      }
      state.regs[insn.rd] = out;
      return true;
    }
    if (insn.kind == RISCVConfigInsnKind::CMv && insn.rd > 0) {
      state.regs[insn.rd] = state.regs[insn.rs2];
      return true;
    }
    if (insn.kind == RISCVConfigInsnKind::CAdd && insn.rd > 0) {
      RISCVConfigValue out;
      if (!riscvConfigAddValues(state.regs[insn.rd], state.regs[insn.rs2],
                                out))
        out = {};
      state.regs[insn.rd] = out;
      return true;
    }
    if (insn.kind == RISCVConfigInsnKind::CSlli && insn.rd > 0) {
      if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer) {
        state.regs[insn.rd] = {};
        return true;
      }
      state.regs[insn.rd] = riscvConfigInteger(
          static_cast<uint32_t>(state.regs[insn.rs1].value) << insn.imm);
      return true;
    }
    if (insn.kind == RISCVConfigInsnKind::CSrli ||
        insn.kind == RISCVConfigInsnKind::CSrai ||
        insn.kind == RISCVConfigInsnKind::CAndi) {
      if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer) {
        state.regs[insn.rd] = {};
        return true;
      }
      uint32_t src = static_cast<uint32_t>(state.regs[insn.rs1].value);
      if (insn.kind == RISCVConfigInsnKind::CSrli)
        state.regs[insn.rd] = riscvConfigInteger(src >> insn.imm);
      else if (insn.kind == RISCVConfigInsnKind::CSrai)
        state.regs[insn.rd] =
            riscvConfigInteger(static_cast<int32_t>(src) >> insn.imm);
      else
        state.regs[insn.rd] =
            riscvConfigInteger(src & static_cast<uint32_t>(insn.imm));
      return true;
    }
    if (insn.kind == RISCVConfigInsnKind::CSub ||
        insn.kind == RISCVConfigInsnKind::CXor ||
        insn.kind == RISCVConfigInsnKind::COr ||
        insn.kind == RISCVConfigInsnKind::CAnd) {
      if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer ||
          state.regs[insn.rs2].kind != RISCVConfigValueKind::Integer) {
        state.regs[insn.rd] = {};
        return true;
      }
      uint32_t lhs = static_cast<uint32_t>(state.regs[insn.rs1].value);
      uint32_t rhs = static_cast<uint32_t>(state.regs[insn.rs2].value);
      uint32_t out = 0;
      if (insn.kind == RISCVConfigInsnKind::CSub)
        out = lhs - rhs;
      else if (insn.kind == RISCVConfigInsnKind::CXor)
        out = lhs ^ rhs;
      else if (insn.kind == RISCVConfigInsnKind::COr)
        out = lhs | rhs;
      else
        out = lhs & rhs;
      state.regs[insn.rd] = riscvConfigInteger(out);
      return true;
    }
    if (insn.load && insn.rd > 0) {
      state.regs[insn.rd] = {};
      return true;
    }
    if (insn.store || isRISCVConfigReturn(insn))
      return true;
    reason = "unsupported-compressed-dataflow";
    return false;
  }

  uint32_t opcode = insn.raw & 0x7f;
  if (opcode == 0x13 && insn.rd > 0) {
    uint32_t funct3 = bits(insn.raw, 14, 12);
    if (funct3 == 0) {
      RISCVConfigValue out;
      if (!riscvConfigAddValues(state.regs[insn.rs1],
                                riscvConfigInteger(insn.imm), out))
        out = {};
      state.regs[insn.rd] = out;
    } else if (funct3 == 7 &&
               state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer) {
      state.regs[insn.rd] = riscvConfigInteger(
          static_cast<uint32_t>(state.regs[insn.rs1].value) &
          static_cast<uint32_t>(insn.imm));
    } else if (funct3 == 1 && bits(insn.raw, 31, 25) == 0 &&
               state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer) {
      state.regs[insn.rd] = riscvConfigInteger(
          static_cast<uint32_t>(state.regs[insn.rs1].value)
          << bits(insn.raw, 24, 20));
    } else if (funct3 == 5 && bits(insn.raw, 31, 25) == 0 &&
               state.regs[insn.rs1].kind == RISCVConfigValueKind::Integer) {
      state.regs[insn.rd] = riscvConfigInteger(
          static_cast<uint32_t>(state.regs[insn.rs1].value) >>
          bits(insn.raw, 24, 20));
    } else {
      state.regs[insn.rd] = {};
    }
    return true;
  }
  if ((opcode == 0x37 || opcode == 0x17) && insn.rd > 0) {
    state.regs[insn.rd] = riscvConfigInteger(insn.imm);
    return true;
  }
  if (opcode == 0x33 && insn.rd > 0) {
    uint32_t funct3 = bits(insn.raw, 14, 12);
    uint32_t funct7 = bits(insn.raw, 31, 25);
    if (state.regs[insn.rs1].kind != RISCVConfigValueKind::Integer ||
        state.regs[insn.rs2].kind != RISCVConfigValueKind::Integer) {
      state.regs[insn.rd] = {};
      return true;
    }
    uint32_t lhs = static_cast<uint32_t>(state.regs[insn.rs1].value);
    uint32_t rhs = static_cast<uint32_t>(state.regs[insn.rs2].value);
    if (funct3 == 0 && funct7 == 0)
      state.regs[insn.rd] = riscvConfigInteger(lhs + rhs);
    else if (funct3 == 0 && funct7 == 0x20)
      state.regs[insn.rd] = riscvConfigInteger(lhs - rhs);
    else if (funct3 == 0 && funct7 == 1)
      state.regs[insn.rd] = riscvConfigInteger(static_cast<uint32_t>(
          static_cast<uint64_t>(lhs) * static_cast<uint64_t>(rhs)));
    else if (funct3 == 4 && funct7 == 0)
      state.regs[insn.rd] = riscvConfigInteger(lhs ^ rhs);
    else if (funct3 == 6 && funct7 == 0)
      state.regs[insn.rd] = riscvConfigInteger(lhs | rhs);
    else if (funct3 == 7 && funct7 == 0)
      state.regs[insn.rd] = riscvConfigInteger(lhs & rhs);
    else
      state.regs[insn.rd] = {};
    return true;
  }
  if (opcode == 0x03 && insn.rd > 0) {
    state.regs[insn.rd] = {};
    return true;
  }
  if (opcode == 0x23 || opcode == 0x63 || opcode == 0x6f ||
      opcode == 0x67 || isRISCVConfigReturn(insn))
    return true;
  reason = "unsupported-dataflow-instruction";
  return false;
}

enum class RISCVConfigInitState { None, Before, After, Maybe };

static StringRef riscvConfigInitStateName(RISCVConfigInitState state) {
  switch (state) {
  case RISCVConfigInitState::None:
    return "none";
  case RISCVConfigInitState::Before:
    return "before-init";
  case RISCVConfigInitState::After:
    return "after-init";
  case RISCVConfigInitState::Maybe:
    return "maybe";
  }
  llvm_unreachable("invalid RISC-V config initialization state");
}

static RISCVConfigInitState
mergeRISCVConfigInitState(RISCVConfigInitState lhs,
                          RISCVConfigInitState rhs) {
  if (lhs == RISCVConfigInitState::None)
    return rhs;
  if (rhs == RISCVConfigInitState::None || lhs == rhs)
    return lhs;
  return RISCVConfigInitState::Maybe;
}

template <class ELFT>
static RISCVConfigUseAuditResult auditRISCVConfigConstantUses(
    const RISCVConfigProofResult &proof,
    ArrayRef<RISCVConfigTrackedGlobal> trackedGlobals,
    ArrayRef<RISCVConfigCallRecord> calls) {
  RISCVConfigUseAuditResult out;
  if (!proof.complete)
    return out;

  DenseMap<Defined *, int64_t> provenValues;
  for (const RISCVConfigTrackedGlobal &g : trackedGlobals) {
    auto it = proof.values.find(g.name);
    if (!g.sym || it == proof.values.end() || !it->second ||
        g.audit.addressTaken || g.audit.unknownPointerUse)
      return out;
    provenValues[g.sym] = *it->second;
  }
  out.provenConstantGlobals = provenValues.size();
  DenseMap<Defined *, uint32_t> readonlyLiveRefs;
  DenseMap<Defined *, uint32_t> readonlyDeadRefs;
  DenseMap<Defined *, uint64_t> readonlySizes;
  DenseSet<Defined *> readonlyAddressTaken;
  auto noteReadonlyRef = [&](InputSectionBase &source, Defined *target,
                             bool countLive, bool dead) {
    if (!target || target->type != STT_OBJECT)
      return;
    auto *targetSec = dyn_cast_or_null<InputSectionBase>(target->section);
    if (!targetSec || (targetSec->flags & SHF_WRITE) ||
        !(targetSec->flags & SHF_ALLOC))
      return;
    if (countLive)
      ++readonlyLiveRefs[target];
    readonlySizes[target] = target->size;
    if (!(source.flags & SHF_EXECINSTR))
      readonlyAddressTaken.insert(target);
    if (dead)
      ++readonlyDeadRefs[target];
  };
  for (ELFFileBase *file : ctx.objectFiles) {
    for (InputSectionBase *sec : file->getSections()) {
      if (!sec || !sec->isLive() || !(sec->flags & SHF_ALLOC) || !sec->file)
        continue;
      RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
      auto scan = [&](auto relRange) {
        for (const auto &rel : relRange)
          noteReadonlyRef(*sec, getRISCVConfigRelocTarget<ELFT>(*sec, rel),
                          true, false);
      };
      scan(rels.rels);
      scan(rels.relas);
    }
  }

  const RISCVConfigCallRecord *initCall = nullptr;
  bool ambiguousInitCall = false;
  for (const RISCVConfigCallRecord &rec : calls) {
    if (!rec.arg0Proven || !rec.arg1Proven)
      continue;
    if (initCall) {
      ambiguousInitCall = true;
      initCall = nullptr;
      break;
    }
    initCall = &rec;
  }

  struct RISCVConfigInitOrderEdge {
    Defined *caller = nullptr;
    Defined *callee = nullptr;
    uint64_t displayOffset = 0;
    uint64_t callerOffset = 0;
  };
  struct RISCVConfigDeadRegionDiag {
    std::string function;
    uint64_t begin = 0;
    uint64_t end = 0;
    bool functionSafe = false;
  };
  SmallVector<RISCVConfigInitOrderEdge, 0> initOrderEdges;
  SmallVector<RISCVConfigDeadRegionDiag, 0> deadRegionDiags;
  DenseMap<Defined *, uint32_t> directIncomingByFunction;
  DenseSet<Defined *> addressTakenFunctions;
  StringMap<Defined *> functionsByName;

  for (ELFFileBase *file : ctx.objectFiles) {
    for (Symbol *sym : file->getSymbols()) {
      Defined *d = dyn_cast_or_null<Defined>(sym);
      if (!d || d->type != STT_FUNC || d->isSection())
        continue;
      if (functionsByName.find(d->getName()) == functionsByName.end())
        functionsByName[d->getName()] = d;
    }
  }

  for (ELFFileBase *file : ctx.objectFiles) {
    for (InputSectionBase *sec : file->getSections()) {
      if (!sec || !sec->isLive() || !(sec->flags & SHF_ALLOC) || !sec->file)
        continue;
      RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
      auto scanEdges = [&](auto relRange) {
        for (const auto &rel : relRange) {
          Defined *target = getRISCVConfigRelocTarget<ELFT>(*sec, rel);
          if (!target || target->type != STT_FUNC)
            continue;
          RelType type = rel.getType(config->isMips64EL);
          if (isRISCVConfigDirectCallRel(type) &&
              (sec->flags & SHF_EXECINSTR)) {
            RISCVConfigFunctionRef caller =
                resolveRISCVFunctionForLocation<ELFT>(*sec, rel.r_offset);
            if (!caller.sym)
              continue;
            uint64_t callerOff = rel.r_offset;
            auto *callerSec =
                dyn_cast_or_null<InputSectionBase>(caller.sym->section);
            if (callerSec && callerSec != sec)
              convertRISCVConfigTargetOffset(*callerSec, *sec, rel.r_offset,
                                             callerOff);
            initOrderEdges.push_back(
                {caller.sym, target, rel.r_offset, callerOff});
            ++directIncomingByFunction[target];
          } else {
            addressTakenFunctions.insert(target);
          }
        }
      };
      scanEdges(rels.rels);
      scanEdges(rels.relas);
    }
  }

  DenseMap<Defined *, RISCVConfigInitState> initEntryStates;
  Defined *initCaller = nullptr;
  if (initCall && !ambiguousInitCall) {
    auto it = functionsByName.find(initCall->caller);
    if (it != functionsByName.end()) {
      initCaller = it->getValue();
      initEntryStates[initCaller] = RISCVConfigInitState::Before;
    }
  }

  std::map<std::pair<Defined *, uint64_t>, RISCVConfigInitState>
      initCallsiteStates;
  auto mergeInitBlockState =
      [](DenseMap<uint64_t, RISCVConfigInitState> &states, uint64_t off,
         RISCVConfigInitState state) {
        RISCVConfigInitState merged =
            mergeRISCVConfigInitState(states.lookup(off), state);
        if (merged == states.lookup(off))
          return false;
        states[off] = merged;
        return true;
      };

  auto recordInitCallsite = [&](Defined *caller, uint64_t off,
                                RISCVConfigInitState state) {
      auto key = std::make_pair(caller, off);
    RISCVConfigInitState oldState = RISCVConfigInitState::None;
    auto oldIt = initCallsiteStates.find(key);
    if (oldIt != initCallsiteStates.end())
      oldState = oldIt->second;
    RISCVConfigInitState merged =
        mergeRISCVConfigInitState(oldState, state);
    if (merged == oldState)
      return false;
    initCallsiteStates[key] = merged;
    return true;
  };

  auto analyzeInitOrderFunction = [&](Defined *func,
                                      RISCVConfigInitState entryState) {
    bool changed = false;
    auto *funcSec = dyn_cast_or_null<InputSectionBase>(func->section);
    if (!funcSec || entryState == RISCVConfigInitState::None)
      return changed;
    std::string cfgReason;
    SmallVector<RISCVConfigBasicBlock, 0> blocks =
        buildRISCVConfigCFG<ELFT>(*funcSec, *func, cfgReason);
    if (blocks.empty())
      return changed;
    DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> relocMap =
        getRISCVConfigRelocs<ELFT>(*funcSec);
    DenseMap<uint64_t, const RISCVConfigBasicBlock *> blockByBegin;
    for (const RISCVConfigBasicBlock &b : blocks)
      blockByBegin[b.begin] = &b;

    DenseMap<uint64_t, RISCVConfigInitState> states;
    SmallVector<uint64_t, 0> wl;
    states[func->value] = entryState;
    wl.push_back(func->value);
    uint32_t iter = 0;
    while (!wl.empty() && ++iter < 10000) {
      uint64_t begin = wl.pop_back_val();
      auto blockIt = blockByBegin.find(begin);
      if (blockIt == blockByBegin.end())
        continue;
      RISCVConfigInitState state = states.lookup(begin);
      const RISCVConfigBasicBlock &block = *blockIt->second;
      SmallVector<std::pair<uint64_t, RISCVConfigInitState>, 2> succs;
      uint64_t skipUntil = 0;
      bool noFallthrough = false;
      for (const RISCVConfigInsn &insn : block.insns) {
        if (insn.off < skipUntil)
          continue;
        uint32_t opcode = insn.raw & 0x7f;
        RISCVConfigDirectCallTarget directCall =
            resolveRISCVConfigDirectCallTarget(*funcSec, insn, relocMap);
        if (directCall.found) {
          if (!directCall.ok) {
            state = RISCVConfigInitState::Maybe;
            continue;
          }
          changed |= recordInitCallsite(func, insn.off, state);
          if (initCall && func == initCaller &&
              insn.off == initCall->callOffset &&
              directCall.target &&
              directCall.target->getName() == initCall->callee)
            state = RISCVConfigInitState::After;
          if (directCall.tail) {
            noFallthrough = true;
            break;
          }
          skipUntil = insn.off + directCall.size;
          continue;
        }
        if (insn.size == 4 && opcode == 0x63) {
          RISCVConfigBranchTarget target =
              resolveRISCVConfigBranchTarget(*funcSec, insn, relocMap);
          if (target.ok)
            succs.push_back({target.target, state});
          succs.push_back({insn.off + insn.size, state});
          noFallthrough = true;
          break;
        }
        if (insn.size == 4 && opcode == 0x6f && insn.rd == 0) {
          RISCVConfigBranchTarget target =
              resolveRISCVConfigJalTarget(*funcSec, insn, relocMap);
          if (target.ok)
            succs.push_back({target.target, state});
          noFallthrough = true;
          break;
        }
        if (insn.size == 2 && isRISCVConfigReturn(insn)) {
          noFallthrough = true;
          break;
        }
        if (insn.size == 2 && insn.kind == RISCVConfigInsnKind::CControlFlow) {
          uint32_t funct3 = bits(insn.raw, 15, 13);
          if (funct3 == 5 || funct3 == 6 || funct3 == 7) {
            RISCVConfigBranchTarget target =
                resolveRISCVConfigRvcControlTarget(
                    *funcSec, insn, relocMap,
                    funct3 == 5 ? R_RISCV_RVC_JUMP : R_RISCV_RVC_BRANCH);
            if (target.ok)
              succs.push_back({target.target, state});
            if (funct3 == 6 || funct3 == 7)
              succs.push_back({insn.off + insn.size, state});
            noFallthrough = true;
            break;
          }
          state = RISCVConfigInitState::Maybe;
        }
        if (opcode == 0x67 || isRISCVConfigReturn(insn)) {
          noFallthrough = true;
          break;
        }
      }
      if (succs.empty() && !noFallthrough &&
          block.end < func->value + func->size)
        succs.push_back({block.end, state});
      for (auto [target, succState] : succs) {
        if (blockByBegin.find(target) == blockByBegin.end())
          continue;
        if (mergeInitBlockState(states, target, succState))
          wl.push_back(target);
      }
    }
    return changed;
  };

  bool changedInitOrder = true;
  while (changedInitOrder) {
    changedInitOrder = false;
    SmallVector<Defined *, 0> workFuncs;
    for (auto [func, state] : initEntryStates)
      if (state != RISCVConfigInitState::None)
        workFuncs.push_back(func);
    for (Defined *func : workFuncs)
      changedInitOrder |= analyzeInitOrderFunction(func,
                                                   initEntryStates.lookup(func));
    for (const RISCVConfigInitOrderEdge &edge : initOrderEdges) {
      auto it = initCallsiteStates.find({edge.caller, edge.callerOffset});
      if (it == initCallsiteStates.end())
        continue;
      RISCVConfigInitState propagated = it->second;
      RISCVConfigInitState merged =
          mergeRISCVConfigInitState(initEntryStates.lookup(edge.callee),
                                    propagated);
      if (merged != initEntryStates.lookup(edge.callee)) {
        initEntryStates[edge.callee] = merged;
        changedInitOrder = true;
      }
    }
  }

  if (initCall && initCaller) {
    uint64_t displayOffset = initCall->callOffset;
    for (const RISCVConfigInitOrderEdge &edge : initOrderEdges)
      if (edge.caller == initCaller && edge.callerOffset == initCall->callOffset &&
          edge.callee->getName() == initCall->callee)
        displayOffset = edge.displayOffset;
    message(Twine("riscv-config-init-order-transition: function=") +
            initCall->caller +
            " call_offset=0x" + Twine::utohexstr(displayOffset) +
            " before=before-init after=after-init"
            " reason=proven-initialization-call");
  }
  for (const RISCVConfigInitOrderEdge &edge : initOrderEdges) {
    auto it = initCallsiteStates.find({edge.caller, edge.callerOffset});
    if (it == initCallsiteStates.end())
      continue;
    RISCVConfigInitState propagated = it->second;
    message(Twine("riscv-config-init-order-edge: caller=") +
            edge.caller->getName() +
            " call_offset=0x" + Twine::utohexstr(edge.displayOffset) +
            " callee=" + edge.callee->getName() +
            " caller_state=" +
            riscvConfigInitStateName(initEntryStates.lookup(edge.caller)) +
            " propagated_state=" + riscvConfigInitStateName(propagated) +
            " kind=direct");
  }

  DenseSet<Defined *> analyzedFunctions;
  for (ELFFileBase *file : ctx.objectFiles) {
    for (InputSectionBase *sec : file->getSections()) {
      if (!sec || !sec->isLive() || !(sec->flags & SHF_EXECINSTR) ||
          !sec->file)
        continue;
      DenseSet<Defined *> funcs;
      RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
      auto collectFuncs = [&](auto relRange) {
        for (const auto &rel : relRange) {
          Defined *d = getRISCVConfigRelocTarget<ELFT>(*sec, rel);
          if (!d)
            continue;
          for (const RISCVConfigTrackedGlobal &g : trackedGlobals) {
            int64_t objectOff = 0;
            if (g.sym &&
                resolveRISCVConfigObjectOffset(d, getRISCVFunctionSplitAddend(rel),
                                               *g.sym, objectOff)) {
              RISCVConfigFunctionRef f =
                  resolveRISCVFunctionForLocation<ELFT>(*sec, rel.r_offset);
              if (f.sym)
                funcs.insert(f.sym);
            }
          }
        }
      };
      collectFuncs(rels.rels);
      collectFuncs(rels.relas);

      for (Defined *func : funcs) {
        if (!analyzedFunctions.insert(func).second)
          continue;
        auto *funcSec = dyn_cast_or_null<InputSectionBase>(func->section);
        if (!funcSec)
          continue;
        uint32_t directIncomingCalls = directIncomingByFunction.lookup(func);
        bool unresolvedIncoming = false;
        bool addressTakenFunction = addressTakenFunctions.contains(func);
        RISCVConfigInitState entryInitState = initEntryStates.lookup(func);
        bool initInternal =
            proof.evaluatedFunctionNames.count(func->getName().str()) != 0;
        ++out.functionsAnalyzed;
        std::string cfgReason;
        SmallVector<RISCVConfigBasicBlock, 0> blocks =
            buildRISCVConfigCFG<ELFT>(*funcSec, *func, cfgReason);
        if (blocks.empty())
          continue;
        DenseMap<uint64_t, SmallVector<RISCVConfigRelocInfo, 0>> relocMap =
            getRISCVConfigRelocs<ELFT>(*funcSec);
        DenseMap<uint64_t, const RISCVConfigBasicBlock *> blockByBegin;
        DenseSet<uint64_t> baselineReachable;
        DenseSet<uint64_t> specializedReachable;
        RISCVConfigDataflowState entryState;
        entryState.valid = true;
        for (auto &r : entryState.regs)
          r = {};
        entryState.regs[0] = riscvConfigInteger(0);
        for (const RISCVConfigBasicBlock &b : blocks)
          blockByBegin[b.begin] = &b;
        bool cfgSafe = true;
        std::string functionReason = "none";
        RISCVConfigInsn unsupportedInsn;
        bool hasUnsupportedInsn = false;
        DenseMap<uint64_t, Defined *> loadSiteSymbols;

        auto runDataflow = [&](bool specialize, DenseSet<uint64_t> &reachable,
                               DenseMap<uint64_t, std::optional<bool>>
                                   &branchResults,
                               DenseSet<uint64_t> *loadSites) {
          DenseMap<uint64_t, RISCVConfigDataflowState> states;
          SmallVector<uint64_t, 0> wl;
          states[func->value] = entryState;
          wl.push_back(func->value);
          uint32_t iter = 0;
          bool safe = true;
          while (!wl.empty() && ++iter < 10000) {
            uint64_t begin = wl.pop_back_val();
            auto blockIt = blockByBegin.find(begin);
            if (blockIt == blockByBegin.end()) {
              if (functionReason == "none")
                functionReason = "missing-basic-block";
              safe = false;
              continue;
            }
            reachable.insert(begin);
            RISCVConfigDataflowState state = states[begin];
            const RISCVConfigBasicBlock &block = *blockIt->second;
            SmallVector<std::pair<uint64_t, RISCVConfigDataflowState>, 2> succs;
            uint64_t skipUntil = 0;
            bool noFallthrough = false;
            for (const RISCVConfigInsn &insn : block.insns) {
              if (insn.off < skipUntil)
                continue;
              uint32_t opcode = insn.raw & 0x7f;
              RISCVConfigDirectCallTarget directCall =
                  resolveRISCVConfigDirectCallTarget(*funcSec, insn, relocMap);
              if (directCall.found) {
                if (!directCall.ok) {
                  if (functionReason == "none")
                    functionReason = directCall.reason;
                  safe = false;
                  break;
                }
                if (directCall.tail) {
                  noFallthrough = true;
                  break;
                }
                constexpr int callerSaved[] = {1,  5,  6,  7,  10, 11,
                                               12, 13, 14, 15, 16, 17,
                                               28, 29, 30, 31};
                for (int r : callerSaved)
                  state.regs[r] = {};
                state.regs[0] = riscvConfigInteger(0);
                skipUntil = insn.off + directCall.size;
                continue;
              }
              if (insn.size == 4 && opcode == 0x63) {
                RISCVConfigBranchTarget target =
                    resolveRISCVConfigBranchTarget(*funcSec, insn, relocMap);
                if (!target.ok) {
                  if (functionReason == "none")
                    functionReason = target.reason;
                  safe = false;
                  break;
                }
                uint64_t fallthrough = insn.off + insn.size;
                bool known = state.regs[insn.rs1].kind ==
                                 RISCVConfigValueKind::Integer &&
                             state.regs[insn.rs2].kind ==
                                 RISCVConfigValueKind::Integer;
                if (known) {
                  bool taken = false;
                  if (!evaluateRISCVConfigBranch(insn.raw,
                                                 state.regs[insn.rs1].value,
                                                 state.regs[insn.rs2].value,
                                                 taken)) {
                    if (functionReason == "none")
                      functionReason = "unsupported-branch-kind";
                    safe = false;
                    break;
                  }
                  auto it = branchResults.find(insn.off);
                  if (it == branchResults.end())
                    branchResults[insn.off] = taken;
                  else if (!it->second || *it->second != taken)
                    branchResults[insn.off] = std::nullopt;
                  succs.push_back({taken ? target.target : fallthrough, state});
                } else {
                  branchResults[insn.off] = std::nullopt;
                  succs.push_back({target.target, state});
                  succs.push_back({fallthrough, state});
                }
                break;
              }
              if (insn.size == 4 && opcode == 0x6f && insn.rd == 0) {
                RISCVConfigBranchTarget target =
                    resolveRISCVConfigJalTarget(*funcSec, insn, relocMap);
                if (!target.ok) {
                  if (functionReason == "none")
                    functionReason = target.reason;
                  safe = false;
                  break;
                }
                succs.push_back({target.target, state});
                noFallthrough = true;
                break;
              }
              if (insn.size == 2 && isRISCVConfigReturn(insn)) {
                noFallthrough = true;
                break;
              }
              if (insn.size == 2 &&
                  insn.kind == RISCVConfigInsnKind::CControlFlow) {
                uint32_t funct3 = bits(insn.raw, 15, 13);
                if (funct3 == 5) {
                  RISCVConfigBranchTarget target =
                      resolveRISCVConfigRvcControlTarget(
                          *funcSec, insn, relocMap, R_RISCV_RVC_JUMP);
                  if (!target.ok) {
                    if (functionReason == "none")
                      functionReason = target.reason;
                    safe = false;
                    break;
                  }
                  succs.push_back({target.target, state});
                  noFallthrough = true;
                  break;
                }
                if (funct3 == 6 || funct3 == 7) {
                  RISCVConfigBranchTarget target =
                      resolveRISCVConfigRvcControlTarget(
                          *funcSec, insn, relocMap, R_RISCV_RVC_BRANCH);
                  if (!target.ok) {
                    if (functionReason == "none")
                      functionReason = target.reason;
                    safe = false;
                    break;
                  }
                  int rs1 = 8 + bits(insn.raw, 9, 7);
                  uint64_t fallthrough = insn.off + insn.size;
                  if (state.regs[rs1].kind == RISCVConfigValueKind::Integer) {
                    bool taken =
                        (static_cast<uint32_t>(state.regs[rs1].value) == 0);
                    if (funct3 == 7)
                      taken = !taken;
                    auto it = branchResults.find(insn.off);
                    if (it == branchResults.end())
                      branchResults[insn.off] = taken;
                    else if (!it->second || *it->second != taken)
                      branchResults[insn.off] = std::nullopt;
                    succs.push_back({taken ? target.target : fallthrough,
                                     state});
                  } else {
                    branchResults[insn.off] = std::nullopt;
                    succs.push_back({target.target, state});
                    succs.push_back({fallthrough, state});
                  }
                  break;
                }
                if (functionReason == "none")
                  functionReason = "unsupported-rvc-control-flow";
                unsupportedInsn = insn;
                hasUnsupportedInsn = true;
                safe = false;
                break;
              }
              if (opcode == 0x67 || isRISCVConfigReturn(insn)) {
                noFallthrough = true;
                break;
              }
              if (insn.size == 4 && opcode == 0x03 &&
                  bits(insn.raw, 14, 12) == 4 && insn.rd > 0) {
                bool loadedTracked = false;
                RISCVConfigValue base = state.regs[insn.rs1];
                auto relIt = relocMap.find(insn.off);
                if (relIt != relocMap.end()) {
                  const RISCVConfigRelocInfo *lo =
                      findRISCVConfigReloc(relIt->second, {R_RISCV_LO12_I});
                  if (lo && lo->target)
                    base = riscvConfigSymbolAddress(lo->target, lo->addend);
                }
                if (base.kind == RISCVConfigValueKind::SymbolAddress) {
                  for (auto [sym, value] : provenValues) {
                    int64_t objectOff = 0;
                    if (resolveRISCVConfigObjectOffset(
                            base.symbol, base.offset + insn.imm, *sym,
                            objectOff) &&
                        objectOff == 0) {
                      if (specialize) {
                        state.regs[insn.rd] = riscvConfigInteger(value);
                        if (loadSites) {
                          loadSites->insert(insn.off);
                          loadSiteSymbols[insn.off] = sym;
                        }
                      } else {
                        state.regs[insn.rd] = {};
                      }
                      loadedTracked = true;
                      break;
                    }
                  }
                }
                if (loadedTracked)
                  continue;
              }
              std::string evalReason;
              if (!evalRISCVConfigIntegerInsn(insn, state, evalReason)) {
                if (functionReason == "none")
                  functionReason = evalReason;
                unsupportedInsn = insn;
                hasUnsupportedInsn = true;
                safe = false;
                break;
              }
              if (insn.size == 4 && (opcode == 0x37 || opcode == 0x17) &&
                  insn.rd > 0) {
                auto it = relocMap.find(insn.off);
                if (it != relocMap.end()) {
                  const RISCVConfigRelocInfo *hi = findRISCVConfigReloc(
                      it->second, {R_RISCV_HI20, R_RISCV_PCREL_HI20});
                  if (hi && hi->target)
                    state.regs[insn.rd] =
                        riscvConfigSymbolAddress(hi->target, hi->addend);
                }
              } else if (insn.size == 4 && opcode == 0x13 && insn.rd > 0) {
                auto it = relocMap.find(insn.off);
                if (it != relocMap.end()) {
                  const RISCVConfigRelocInfo *lo = findRISCVConfigReloc(
                      it->second, {R_RISCV_LO12_I, R_RISCV_PCREL_LO12_I});
                  if (lo && lo->target)
                    state.regs[insn.rd] =
                        riscvConfigSymbolAddress(lo->target, lo->addend);
                }
              }
            }
            if (succs.empty() && !noFallthrough &&
                block.end < func->value + func->size)
              succs.push_back({block.end, state});
            for (auto &[target, succState] : succs) {
              if (blockByBegin.find(target) == blockByBegin.end())
                continue;
              if (mergeRISCVConfigState(states[target], succState))
                wl.push_back(target);
            }
          }
          if (iter >= 10000 && functionReason == "none")
            functionReason = "dataflow-iteration-limit";
          return safe && iter < 10000;
        };

        DenseMap<uint64_t, std::optional<bool>> baselineBranchResults;
        DenseMap<uint64_t, std::optional<bool>> specializedBranchResults;
        DenseSet<uint64_t> specializedLoadSites;
        cfgSafe &= runDataflow(false, baselineReachable, baselineBranchResults,
                               nullptr);
        cfgSafe &= runDataflow(true, specializedReachable,
                               specializedBranchResults,
                               &specializedLoadSites);
        if (!cfgSafe && functionReason == "none")
          functionReason = "dataflow-unsafe";
        if (cfgSafe)
          ++out.cfgSafeFunctions;

        out.constantLoads += specializedLoadSites.size();
        for (uint64_t off : specializedLoadSites) {
          Defined *sym = loadSiteSymbols.lookup(off);
          bool initOrderSafe =
              initInternal || entryInitState == RISCVConfigInitState::After;
          if (!initOrderSafe)
            ++out.unsafeOrUnknownReadSites;
          message(Twine("riscv-config-constant-load: function=") +
                  func->getName() +
                  " offset=0x" + Twine::utohexstr(off) +
                  " symbol=" + (sym ? Twine(sym->getName()) : Twine("unknown")) +
                  " value=" +
                  (sym && provenValues.find(sym) != provenValues.end()
                       ? Twine(provenValues.lookup(sym))
                       : Twine("unknown")) +
                  " safe=1 reason=tracked-global");
          message(Twine("riscv-config-init-order: read_function=") +
                  func->getName() +
                  " read_offset=0x" + Twine::utohexstr(off) +
                  " category=" +
                  (initInternal ? Twine("initialization-internal")
                                : Twine("post-init-reader")) +
                  " incoming_state=" +
                  riscvConfigInitStateName(initInternal
                                               ? RISCVConfigInitState::After
                                               : entryInitState) +
                  " safe=" + Twine(initOrderSafe ? 1 : 0));
        }

        for (const auto &kv : specializedBranchResults) {
          uint64_t off = kv.first;
          std::optional<bool> specialized = kv.second;
          if (!specialized)
            continue;
          ++out.constantBranches;
          if (*specialized)
            ++out.alwaysTakenBranches;
          else
            ++out.neverTakenBranches;
          auto baseIt = baselineBranchResults.find(off);
          std::optional<bool> baseline;
          if (baseIt != baselineBranchResults.end())
            baseline = baseIt->second;
          bool dependent = !baseline || *baseline != *specialized;
          if (dependent)
            ++out.specializationDependentBranches;
          message(Twine("riscv-config-constant-branch: function=") +
                  func->getName() +
                  " offset=0x" + Twine::utohexstr(off) +
                  " kind=unknown lhs=unknown rhs=unknown result=" +
                  (*specialized ? Twine("taken") : Twine("not-taken")) +
                  " baseline_result=" +
                  (baseline ? (*baseline ? Twine("taken") : Twine("not-taken"))
                            : Twine("unknown")) +
                  " specialized_result=" +
                  (*specialized ? Twine("taken") : Twine("not-taken")) +
                  " specialization_dependent=" + Twine(dependent ? 1 : 0) +
                  " target=unknown fallthrough=unknown source_globals=unknown");
        }

        uint32_t functionDeadBlocks = 0;
        uint64_t functionDeadBytes = 0;

        uint64_t candidateBytes = 0;
        for (const RISCVConfigBasicBlock &b : blocks) {
          if (baselineReachable.contains(b.begin) &&
              !specializedReachable.contains(b.begin) && b.begin != func->value) {
            ++out.candidateDeadRegions;
            ++functionDeadBlocks;
            candidateBytes += b.end - b.begin;
            functionDeadBytes += b.end - b.begin;
            bool functionSafe =
                cfgSafe &&
                (initInternal || entryInitState == RISCVConfigInitState::After);
            deadRegionDiags.push_back(
                {func->getName().str(), b.begin, b.end, functionSafe});
            for (const auto &kv : relocMap) {
              if (kv.first < b.begin || kv.first >= b.end)
                continue;
              for (const RISCVConfigRelocInfo &r : kv.second)
                noteReadonlyRef(*funcSec, r.target, false, true);
            }
          }
        }
        out.potentialDeadTextBytes += candidateBytes;
        message(Twine("riscv-config-differential-function: function=") +
                func->getName() +
                " baseline_reachable_blocks=" +
                Twine(baselineReachable.size()) +
                " specialized_reachable_blocks=" +
                Twine(specializedReachable.size()) +
                " specialization_dead_blocks=" + Twine(functionDeadBlocks) +
                " specialization_dead_bytes=" + Twine(functionDeadBytes) +
                " cfg_safe=" + Twine(cfgSafe ? 1 : 0) +
                " reason=" + functionReason);
        if (!cfgSafe && hasUnsupportedInsn && unsupportedInsn.size == 2) {
          message(Twine("riscv-config-dataflow-unsupported: function=") +
                  func->getName() +
                  " offset=0x" + Twine::utohexstr(unsupportedInsn.off) +
                  " raw16=0x" + Twine::utohexstr(unsupportedInsn.raw) +
                  " quadrant=" + Twine(unsigned(unsupportedInsn.raw & 3)) +
                  " funct3=" +
                  Twine(unsigned(bits(unsupportedInsn.raw, 15, 13))) +
                  " bit12=" +
                  Twine(unsigned(bits(unsupportedInsn.raw, 12, 12))) +
                  " decoded_kind=" +
                  riscvConfigInsnKindName(unsupportedInsn.kind) +
                  " reason=" + functionReason);
        }
        message(Twine("riscv-config-function-audit: function=") +
                func->getName() +
                " cfg_safe=" + Twine(cfgSafe ? 1 : 0) +
                " reason=" + functionReason);
        message(Twine("riscv-config-init-order-function: function=") +
                func->getName() +
                " address_taken=" + Twine(addressTakenFunction ? 1 : 0) +
                " preemptible=0" +
                " unresolved_incoming=" + Twine(unresolvedIncoming ? 1 : 0) +
                " direct_incoming_calls=" + Twine(directIncomingCalls) +
                " entry_state=" +
                riscvConfigInitStateName(initInternal
                                             ? RISCVConfigInitState::After
                                             : entryInitState) +
                " reason=" +
                (initInternal
                     ? Twine("initialization-chain-internal")
                     : (entryInitState == RISCVConfigInitState::After
                            ? Twine("closed-world-direct-call-closure")
                            : Twine("not-proven-after-initialization"))));
      }
    }
  }
  out.initializationOrderProven = out.unsafeOrUnknownReadSites == 0;
  for (const RISCVConfigDeadRegionDiag &diag : deadRegionDiags) {
    bool regionSafe = out.initializationOrderProven && diag.functionSafe;
    if (regionSafe) {
      ++out.safeDeadRegions;
      out.conservativeDeadTextBytes += diag.end - diag.begin;
    }
    message(Twine("riscv-config-dead-region: function=") + diag.function +
            " begin=0x" + Twine::utohexstr(diag.begin) +
            " end=0x" + Twine::utohexstr(diag.end) +
            " bytes=" + Twine(diag.end - diag.begin) +
            " safe=" + Twine(regionSafe ? 1 : 0) +
            " reason=" +
            (regionSafe
                 ? Twine("none")
                 : (diag.functionSafe
                        ? Twine("global-initialization-order-not-proven")
                        : Twine("function-safety-not-proven"))) +
            " controlling_branches=unknown");
  }
  for (auto [sym, liveRefs] : readonlyLiveRefs) {
    uint32_t deadRefs = readonlyDeadRefs.lookup(sym);
    if (liveRefs != 0 && liveRefs == deadRefs &&
        !readonlyAddressTaken.contains(sym))
      out.potentialDeadRodataBytes += readonlySizes.lookup(sym);
  }
  return out;
}

template <class ELFT>
static void auditRISCVConfigRodata(StringRef name,
                                   RISCVConfigRodataAudit &audit) {
  bool ambiguous = false;
  Defined *targetSym =
      findUniqueRISCVConfigDefinedByName<ELFT>(name, STT_OBJECT, ambiguous);
  if (!targetSym) {
    if (ambiguous)
      message(Twine("riscv-config-rodata: symbol=") + name +
              " ambiguous=1");
    return;
  }
  audit.name = name.str();
  audit.size = targetSym->size;
  for (ELFFileBase *file : ctx.objectFiles) {
    for (InputSectionBase *sec : file->getSections()) {
      if (!sec || !sec->isLive() || !sec->file)
        continue;
      RelsOrRelas<ELFT> rels = sec->template relsOrRelas<ELFT>();
      auto scan = [&](auto relsRange) {
        for (const auto &rel : relsRange) {
          if (!riscvConfigRelocTargetsObject<ELFT>(*sec, rel, *targetSym))
            continue;
          ++audit.liveReferenceCount;
          RISCVConfigFunctionRef ref =
              resolveRISCVFunctionForLocation<ELFT>(*sec, rel.r_offset);
          if (!ref.sym)
            dumpRISCVConfigResolverDebug<ELFT>(*sec, rel.r_offset);
          audit.referenceFunctions.insert(ref.name);
          if (!(sec->flags & SHF_EXECINSTR))
            audit.addressTaken = true;
          RISCVConfigInsn insn = decodeRISCVConfigInsn(sec->content(),
                                                       rel.r_offset);
          if (insn.load && insn.rs1 != 0)
            audit.dynamicIndex = true;
        }
      };
      scan(rels.rels);
      scan(rels.relas);
    }
  }
  SmallVector<std::string, 0> refs(audit.referenceFunctions.begin(),
                                   audit.referenceFunctions.end());
  bool fullyDeadCandidate = audit.liveReferenceCount == 0;
  bool partial = audit.liveReferenceCount != 0 && audit.dynamicIndex;
  message(Twine("riscv-config-rodata: symbol=") + audit.name +
          " size=" + Twine(audit.size) +
          " live_reference_count=" + Twine(audit.liveReferenceCount) +
          " reference_functions=" +
          (refs.empty() ? Twine("none") : Twine(llvm::join(refs, ","))) +
          " address_taken=" + Twine(audit.addressTaken ? 1 : 0) +
          " dynamic_index=" + Twine(audit.dynamicIndex ? 1 : 0) +
          " references_from_dead_candidate_regions=0" +
          " potentially_fully_dead=" + Twine(fullyDeadCandidate ? 1 : 0) +
          " potentially_partially_reducible=" + Twine(partial ? 1 : 0));
}

template <class ELFT> static void printRISCVConfigSpecializationAudit() {
  if (!config->printRISCVConfigSpecializationAudit ||
      config->emachine != EM_RISCV)
    return;

  SmallVector<RISCVConfigCallRecord, 0> calls;
  printRISCVConfigCallsiteAudit<ELFT>("initeccsize", calls);
  uint32_t provenCalls = 0, unknownCalls = 0;
  std::set<std::pair<int64_t, int64_t>> argSets;
  for (const RISCVConfigCallRecord &rec : calls) {
    if (rec.arg0Proven && rec.arg1Proven) {
      ++provenCalls;
      argSets.insert({rec.arg0Value, rec.arg1Value});
    } else {
      ++unknownCalls;
    }
  }
  message(Twine("riscv-config-callsite-summary: callee=initeccsize") +
          " live_direct_calls=" + Twine(calls.size()) +
          " proven_constant_calls=" + Twine(provenCalls) +
          " unknown_calls=" + Twine(unknownCalls) +
          " distinct_constant_argument_sets=" + Twine(argSets.size()));

  constexpr StringLiteral globals[] = {
      "VERSION", "WD",       "WDB",      "ECCLEVEL",
      "neccblk1", "neccblk2", "datablkw", "eccblkwid"};
  constexpr size_t globalCount = sizeof(globals) / sizeof(globals[0]);
  uint32_t candidateSafeGlobals = 0;
  SmallVector<RISCVConfigTrackedGlobal, 0> trackedGlobals;
  for (StringRef name : globals) {
    RISCVConfigGlobalAudit audit;
    auditRISCVConfigGlobal<ELFT>(name, audit);
    bool ambiguous = false;
    Defined *sym =
        findUniqueRISCVConfigDefinedByName<ELFT>(name, STT_OBJECT, ambiguous);
    if (sym && !ambiguous)
      trackedGlobals.push_back({sym, name.str(), audit});
    if (!audit.name.empty() && !audit.addressTaken && !audit.unknownPointerUse &&
        !audit.writerFunctions.empty() && audit.writerFunctions.size() <= 2)
      ++candidateSafeGlobals;
  }

  constexpr StringLiteral rodataSyms[] = {"eccblocks", "vpat",  "fmtword",
                                          "adelta",    "g0exp", "g0log"};
  SmallVector<RISCVConfigRodataAudit, 0> rodataAudits;
  bool eccblocksDead = false, vpatDead = false;
  for (StringRef name : rodataSyms) {
    RISCVConfigRodataAudit audit;
    auditRISCVConfigRodata<ELFT>(name, audit);
    if (!audit.name.empty())
      rodataAudits.push_back(audit);
  }

  RISCVConfigProofResult proof =
      tryEvaluateRISCVConfigInitialization<ELFT>(calls, trackedGlobals);
  auto valueOrUnknown = [&](StringRef name) -> Twine {
    auto it = proof.values.find(name.str());
    if (it == proof.values.end() || !it->second)
      return Twine("unknown");
    return Twine(*it->second);
  };
  message(Twine("riscv-config-proof: entry=initeccsize constant_args=") +
          Twine(argSets.size() == 1 ? 1 : 0) +
          " VERSION=" + valueOrUnknown("VERSION") +
          " WD=" + valueOrUnknown("WD") +
          " WDB=" + valueOrUnknown("WDB") +
          " ECCLEVEL=" + valueOrUnknown("ECCLEVEL") +
          " neccblk1=" + valueOrUnknown("neccblk1") +
          " neccblk2=" + valueOrUnknown("neccblk2") +
          " datablkw=" + valueOrUnknown("datablkw") +
          " eccblkwid=" + valueOrUnknown("eccblkwid") +
          " proof_complete=" + Twine(proof.complete ? 1 : 0) +
          " rejection_reason=" + proof.reason);
  message(Twine("riscv-config-evaluator: entry=initeccsize") +
          " visited_blocks=" + Twine(proof.visitedBlocks) +
          " executed_instructions=" + Twine(proof.executedInstructions) +
          " loop_iterations=" + Twine(proof.loopIterations) +
          " readonly_loads=" + Twine(proof.readonlyLoads) +
          " tracked_stores=" + Twine(proof.trackedStores) +
          " evaluator_constant_branches=" + Twine(proof.constantBranches) +
          " evaluator_always_taken=" + Twine(proof.alwaysTakenBranches) +
          " evaluator_never_taken=" + Twine(proof.neverTakenBranches) +
          " direct_calls=" + Twine(proof.directCalls) +
          " abstract_calls=" + Twine(proof.abstractCalls) +
          " functions_evaluated=" + Twine(proof.functionsEvaluated) +
          " final_status=" + (proof.complete ? Twine("complete")
                                             : Twine("failed")) +
          " rejection_reason=" + proof.reason +
          " function=" +
          (proof.failFunction.empty() ? Twine("none")
                                      : Twine(proof.failFunction)) +
          " offset=0x" + Twine::utohexstr(proof.failOffset) +
          " opcode=0x" + Twine::utohexstr(proof.failOpcode) +
          " raw16=0x" + Twine::utohexstr(proof.failRaw16) +
          " quadrant=" + Twine(unsigned(proof.failQuadrant)) +
          " funct3=" + Twine(unsigned(proof.failFunct3)) +
          " bit12=" + Twine(unsigned(proof.failBit12)) +
          " rd_rs1=" + Twine(proof.failRd) +
          " rs2=" + Twine(proof.failRs2) +
          " decoded_kind=" + riscvConfigInsnKindName(proof.failKind));

  RISCVConfigUseAuditResult useAudit =
      auditRISCVConfigConstantUses<ELFT>(proof, trackedGlobals, calls);
  uint64_t candidateInitializationRodataBytes = 0;
  for (const RISCVConfigRodataAudit &audit : rodataAudits) {
    bool ambiguous = false;
    Defined *sym =
        findUniqueRISCVConfigDefinedByName<ELFT>(audit.name, STT_OBJECT,
                                                 ambiguous);
    bool allRefsInInit = !audit.referenceFunctions.empty() &&
                         llvm::all_of(audit.referenceFunctions,
                                      [&](const std::string &name) {
                                        return proof.evaluatedFunctionNames
                                            .count(name) != 0;
                                      });
    bool resolvedByProof = sym && proof.readonlySourceObjects.count(sym) != 0;
    bool candidate = allRefsInInit && resolvedByProof && !audit.addressTaken;
    if (candidate)
      candidateInitializationRodataBytes += audit.size;
    message(Twine("riscv-config-init-rodata-candidate: symbol=") +
            audit.name +
            " size=" + Twine(audit.size) +
            " all_refs_in_initialization_chain=" +
            Twine(allRefsInInit ? 1 : 0) +
            " resolved_by_proof=" + Twine(resolvedByProof ? 1 : 0) +
            " candidate=" + Twine(candidate ? 1 : 0));
    if (audit.name == "eccblocks" && candidate)
      eccblocksDead = true;
    if (audit.name == "vpat" && candidate)
      vpatDead = true;
  }
  useAudit.candidateInitializationRodataBytes =
      candidateInitializationRodataBytes;
  useAudit.potentialDeadRodataBytes = 0;
  useAudit.conservativeDeadRodataBytes = 0;
  message(Twine("riscv-config-constant-use-summary: proven_constant_globals=") +
          Twine(useAudit.provenConstantGlobals) +
          " unique_constant_loads=" + Twine(useAudit.constantLoads) +
          " unique_constant_branches=" + Twine(useAudit.constantBranches) +
          " specialization_dependent_branches=" +
          Twine(useAudit.specializationDependentBranches) +
          " always_taken_branches=" + Twine(useAudit.alwaysTakenBranches) +
          " never_taken_branches=" + Twine(useAudit.neverTakenBranches) +
          " functions_analyzed=" + Twine(useAudit.functionsAnalyzed) +
          " cfg_safe_functions=" + Twine(useAudit.cfgSafeFunctions) +
          " candidate_dead_regions=" + Twine(useAudit.candidateDeadRegions) +
          " safe_dead_regions=" + Twine(useAudit.safeDeadRegions) +
          " potential_dead_text_bytes=" +
          Twine(useAudit.potentialDeadTextBytes) +
          " conservative_dead_text_bytes=" +
          Twine(useAudit.conservativeDeadTextBytes) +
          " potential_dead_rodata_bytes=" +
          Twine(useAudit.potentialDeadRodataBytes) +
          " conservative_dead_rodata_bytes=" +
          Twine(useAudit.conservativeDeadRodataBytes) +
          " candidate_initialization_rodata_bytes=" +
          Twine(useAudit.candidateInitializationRodataBytes) +
          " initialization_order_proven=" +
          Twine(useAudit.initializationOrderProven ? 1 : 0) +
          " unsafe_or_unknown_read_sites=" +
          Twine(useAudit.unsafeOrUnknownReadSites));

  message(Twine("riscv-config-specialization-summary: candidate_entry=initeccsize") +
          " live_calls=" + Twine(calls.size()) +
          " constant_calls=" + Twine(provenCalls) +
          " unique_argument_set=" + Twine(argSets.size() == 1 ? 1 : 0) +
          " config_globals=" + Twine(globalCount) +
          " candidate_writer_set_safe_globals=" +
          Twine(candidateSafeGlobals) +
          " proven_constant_globals=" +
          Twine(useAudit.provenConstantGlobals) +
          " unique_constant_loads=" + Twine(useAudit.constantLoads) +
          " unique_constant_branches=" + Twine(useAudit.constantBranches) +
          " specialization_dependent_branches=" +
          Twine(useAudit.specializationDependentBranches) +
          " always_taken_branches=" + Twine(useAudit.alwaysTakenBranches) +
          " never_taken_branches=" + Twine(useAudit.neverTakenBranches) +
          " safe_dead_regions=" + Twine(useAudit.safeDeadRegions) +
          " potential_dead_text_bytes=" +
          Twine(useAudit.potentialDeadTextBytes) +
          " potential_dead_rodata_bytes=" +
          Twine(useAudit.potentialDeadRodataBytes) +
          " candidate_initialization_rodata_bytes=" +
          Twine(useAudit.candidateInitializationRodataBytes) +
          " candidate_total_opportunity_bytes=" +
          Twine(useAudit.potentialDeadTextBytes +
                useAudit.potentialDeadRodataBytes +
                useAudit.candidateInitializationRodataBytes) +
          " conservative_total_opportunity_bytes=" +
          Twine(useAudit.conservativeDeadTextBytes +
                useAudit.conservativeDeadRodataBytes) +
          " initialization_order_proven=" +
          Twine(useAudit.initializationOrderProven ? 1 : 0) +
          " unsafe_or_unknown_read_sites=" +
          Twine(useAudit.unsafeOrUnknownReadSites) +
          " eccblocks_fully_dead_candidate=" +
          Twine(eccblocksDead ? 1 : 0) +
          " vpat_fully_dead_candidate=" + Twine(vpatDead ? 1 : 0) +
          " transformation_recommended=" +
          Twine((useAudit.potentialDeadTextBytes +
                 useAudit.potentialDeadRodataBytes +
                 useAudit.candidateInitializationRodataBytes) > 0
                    ? 1
                    : 0) +
          " transformation_safety_proven=" +
          Twine(useAudit.initializationOrderProven &&
                        useAudit.conservativeDeadTextBytes != 0
                    ? 1
                    : 0) +
          " rejection_reason_counts=" + proof.reason + ":1");
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

  // Garbage collection and removal of shared symbols from unused shared objects.
  invokeELFT(markLive,);
  printRISCVFunctionSplitGCStats();
  invokeELFT(printRISCVConfigSpecializationAudit,);
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
