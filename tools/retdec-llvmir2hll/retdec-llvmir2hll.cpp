/**
 * @file src/llvmir2hlltool/llvmir2hll.cpp
 * @brief Convertor of LLVM IR into the specified target high-level language.
 * @copyright (c) 2017 Avast Software, licensed under the MIT license
 *
 * The implementation of this tool is based on llvm/tools/llc/llc.cpp.
 */

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <future>
#include <iostream>
#include <llvm/Support/Casting.h>
#include <llvm/Support/raw_ostream.h>
#include <memory>
#include <ostream>
#include <thread>

#include <llvm/ADT/Triple.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/InitializePasses.h>
#include <llvm/MC/SubtargetFeature.h>
#include <llvm/Pass.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/ErrorHandling.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/Host.h>
#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/PluginLoader.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>
// #include <llvm/Support/TargetRegistry.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Target/TargetMachine.h>

#include "retdec-llvmir2hll/analysis/alias_analysis/alias_analysis.h"
#include "retdec-llvmir2hll/analysis/alias_analysis/alias_analysis_factory.h"
#include "retdec-llvmir2hll/analysis/value_analysis.h"
#include "retdec-llvmir2hll/config/configs/json_config.h"
#include "retdec-llvmir2hll/evaluator/arithm_expr_evaluator.h"
#include "retdec-llvmir2hll/evaluator/arithm_expr_evaluator_factory.h"
#include "retdec-llvmir2hll/graphs/cfg/cfg_builders/non_recursive_cfg_builder.h"
#include "retdec-llvmir2hll/graphs/cfg/cfg_writer.h"
#include "retdec-llvmir2hll/graphs/cfg/cfg_writer_factory.h"
#include "retdec-llvmir2hll/graphs/cg/cg_builder.h"
#include "retdec-llvmir2hll/graphs/cg/cg_writer.h"
#include "retdec-llvmir2hll/graphs/cg/cg_writer_factory.h"
#include "retdec-llvmir2hll/hll/hll_writer.h"
#include "retdec-llvmir2hll/hll/hll_writer_factory.h"
#include "retdec-llvmir2hll/ir/function.h"
#include "retdec-llvmir2hll/ir/module.h"
#include "retdec-llvmir2hll/llvm/llvm_debug_info_obtainer.h"
#include "retdec-llvmir2hll/llvm/llvm_intrinsic_converter.h"
#include "retdec-llvmir2hll/llvm/llvmir2bir_converter.h"
#include "retdec-llvmir2hll/obtainer/call_info_obtainer.h"
#include "retdec-llvmir2hll/obtainer/call_info_obtainer_factory.h"
#include "retdec-llvmir2hll/optimizer/optimizer_manager.h"
#include "retdec-llvmir2hll/pattern/pattern_finder_factory.h"
#include "retdec-llvmir2hll/pattern/pattern_finder_runner.h"
#include "retdec-llvmir2hll/pattern/pattern_finder_runners/cli_pattern_finder_runner.h"
#include "retdec-llvmir2hll/pattern/pattern_finder_runners/no_action_pattern_finder_runner.h"
#include "retdec-llvmir2hll/semantics/semantics/compound_semantics_builder.h"
#include "retdec-llvmir2hll/semantics/semantics/default_semantics.h"
#include "retdec-llvmir2hll/semantics/semantics_factory.h"
#include "retdec-llvmir2hll/support/const_symbol_converter.h"
#include "retdec-llvmir2hll/support/debug.h"
#include "retdec-llvmir2hll/support/expr_types_fixer.h"
// #include "retdec/bin2llvmir/analyses/symbolic_tree.h"
// #include "retdec/bin2llvmir/providers/abi/abi.h"
// #include "retdec/common/architecture.h"
// #include "retdec-llvmir2hll/support/funcs_with_prefix_remover.h"
#include "retdec-llvmir2hll/llvmir2hll.h"
#include "retdec-llvmir2hll/support/library_funcs_remover.h"
#include "retdec-llvmir2hll/support/smart_ptr.h"
#include "retdec-llvmir2hll/support/unreachable_code_in_cfg_remover.h"
#include "retdec-llvmir2hll/utils/ir.h"
#include "retdec-llvmir2hll/utils/string.h"
#include "retdec-llvmir2hll/validator/validator.h"
#include "retdec-llvmir2hll/validator/validator_factory.h"
#include "retdec-llvmir2hll/var_name_gen/var_name_gen_factory.h"
#include "retdec-llvmir2hll/var_name_gen/var_name_gens/num_var_name_gen.h"
#include "retdec-llvmir2hll/var_renamer/var_renamer.h"
#include "retdec-llvmir2hll/var_renamer/var_renamer_factory.h"
// #include "retdec/bin2llvmir/optimizations/provider_init/provider_init.h"
// #include "retdec/bin2llvmir/providers/config.h"
// #include "retdec/llvm-support/diagnostics.h"
#include "retdec-llvmir2hll/retdec-config/config.h"
#include "retdec-llvmir2hll/retdec-utils/binary_path.h"
#include "retdec-llvmir2hll/retdec-utils/container.h"
#include "retdec-llvmir2hll/retdec-utils/conversion.h"
#include "retdec-llvmir2hll/retdec-utils/filesystem.h"
#include "retdec-llvmir2hll/retdec-utils/io/log.h"
#include "retdec-llvmir2hll/retdec-utils/memory.h"
#include "retdec-llvmir2hll/retdec-utils/string.h"
#include "retdec-llvmir2hll/retdec-utils/version.h"

using namespace llvm;

using retdec::llvmir2hll::ShPtr;
using retdec::utils::hasItem;
using retdec::utils::joinStrings;
using retdec::utils::limitSystemMemory;
using retdec::utils::limitSystemMemoryToHalfOfTotalSystemMemory;
using retdec::utils::split;
using retdec::utils::strToNum;

const bool Debug = true;

//
//==============================================================================
// Program options
//==============================================================================
//

class ProgramOptions {
public:
  std::string programName;
  retdec::config::Config &config;
  retdec::config::Parameters &params;
  std::list<std::string> _argv;

  std::string mode = "bin";
  uint64_t bitSize = 32;
  std::string arExtractPath;
  std::string arName;
  std::optional<uint64_t> arIdx;

  bool cleanup = false;
  std::set<std::string> toClean;

public:
  ProgramOptions(int argc, char *argv[], retdec::config::Config &c,
                 retdec::config::Parameters &p);

  void load();

private:
  void loadOption(std::list<std::string>::iterator &i);
  bool isParam(std::list<std::string>::iterator i, const std::string &shortp,
               const std::string &longp = std::string());
  std::string getParamOrDie(std::list<std::string>::iterator &i);
  void printHelpAndDie();
  void afterLoad();
  std::string checkFile(const std::string &path,
                        const std::string &errorMsgPrefix);
};

ProgramOptions::ProgramOptions(int argc, char *argv[],
                               retdec::config::Config &c,
                               retdec::config::Parameters &p)
    : config(c), params(p) {
  if (argc > 0) {
    programName = argv[0];
  }

  for (int i = 1; i < argc; ++i) {
    _argv.push_back(argv[i]);
  }
}

void ProgramOptions::load() {
  for (auto i = _argv.begin(); i != _argv.end();) {
    // Load config if specified.
    if (isParam(i, "", "--config")) {
      auto backup = config.parameters;
      auto file = getParamOrDie(i);
      file = checkFile(file, "[--config]");

      try {
        config = retdec::config::Config::fromFile(file);
      } catch (const retdec::config::ParseException &e) {
        throw std::runtime_error("[--config] loading of config failed: " +
                                 std::string(e.what()));
      }

      // TODO:
      // This redefines all the params from the loaded config.
      // Maybe we should do some kind of merge.
      // But it is hard to know what was defined, what was not,
      // and which value to prefer.
      config.parameters = backup;
    }
    ++i;
  }

  for (auto i = _argv.begin(); i != _argv.end();) {
    loadOption(i);
    if (i != _argv.end()) {
      ++i;
    }
  }

  afterLoad();
}

void ProgramOptions::loadOption(std::list<std::string>::iterator &i) {
  std::string c = *i;

  if (isParam(i, "-h", "--help")) {
    printHelpAndDie();
  } else if (isParam(i, "", "--version")) {
    Log::info() << retdec::utils::version::getVersionStringLong() << "\n";
    exit(EXIT_SUCCESS);
  } else if (isParam(i, "", "--print-after-all")) {
    llvm::StringMap<llvm::cl::Option *> &opts =
        llvm::cl::getRegisteredOptions();

    auto *paa = static_cast<llvm::cl::opt<bool> *>(opts["print-after-all"]);
    paa->setInitialValue(true);
  } else if (isParam(i, "", "--print-before-all")) {
    llvm::StringMap<llvm::cl::Option *> &opts =
        llvm::cl::getRegisteredOptions();

    auto *paa = static_cast<llvm::cl::opt<bool> *>(opts["print-before-all"]);
    paa->setInitialValue(true);
  } else if (isParam(i, "-m", "--mode")) {
    auto m = getParamOrDie(i);
    if (!(m == "bin" || m == "raw")) {
      throw std::runtime_error("[-m|--mode] unknown mode: " + m);
    }
    mode = m;
  } else if (isParam(i, "-b", "--bit-size")) {
    auto val = getParamOrDie(i);
    try {
      bitSize = std::stoull(val);
      if (!(bitSize == 16 || bitSize == 32 || bitSize == 64)) {
        throw std::runtime_error("");
      }
    } catch (...) {
      throw std::runtime_error("[-b|--bit-size] invalid value: " + val);
    }
  } else if (isParam(i, "-a", "--arch")) {
    auto a = getParamOrDie(i);
    if (!(a == "mips" || a == "pic32" || a == "arm" || a == "thumb" ||
          a == "arm64" || a == "powerpc" || a == "x86" || a == "x86-64")) {
      throw std::runtime_error("[-a|--arch] unknown architecture: " + a);
    }
    config.architecture.setName(a);
  } else if (isParam(i, "-e", "--endian")) {
    auto e = getParamOrDie(i);
    if (e == "little") {
      config.architecture.setIsEndianLittle();
    } else if (e == "big") {
      config.architecture.setIsEndianBig();
    } else {
      throw std::runtime_error("[-e|--endian] unknown endian: " + e);
    }
  } else if (isParam(i, "-f", "--output-format")) {
    auto of = getParamOrDie(i);
    if (!(of == "plain" || of == "json" || of == "json-human")) {
      throw std::runtime_error("[-f|--output-format] unknown output format: " +
                               of);
    }
    config.parameters.setOutputFormat(of);
  } else if (isParam(i, "", "--max-memory")) {
    auto val = getParamOrDie(i);
    try {
      params.setMaxMemoryLimit(std::stoull(val));
      params.setIsMaxMemoryLimitHalfRam(false);
    } catch (...) {
      throw std::runtime_error("[--max-memory] invalid value: " + val);
    }
  } else if (isParam(i, "", "--no-memory-limit")) {
    params.setMaxMemoryLimit(0);
    params.setIsMaxMemoryLimitHalfRam(false);
  } else if (isParam(i, "-o", "--output")) {
    std::string out = getParamOrDie(i);
    params.setOutputFile(out);

    auto lastDot = out.find_last_of('.');
    if (lastDot != std::string::npos) {
      out = out.substr(0, lastDot);
    }
    params.setOutputAsmFile(out + ".dsm");
    params.setOutputBitcodeFile(out + ".bc");
    params.setOutputLlvmirFile(out + ".ll");
    params.setOutputConfigFile(out + ".config.json");
    params.setOutputUnpackedFile(out + "-unpacked");
    arExtractPath = out + "-extracted";
  } else if (isParam(i, "-k", "--keep-unreachable-funcs")) {
    params.setIsKeepAllFunctions(true);
  } else if (isParam(i, "-p", "--pdb")) {
    std::string pdb = checkFile(getParamOrDie(i), "[-p|--pdb]");
    config.parameters.setInputPdbFile(pdb);
  } else if (isParam(i, "", "--select-ranges")) {
    std::stringstream ranges(getParamOrDie(i));
    while (ranges.good()) {
      std::string range;
      getline(ranges, range, ',');
      auto r = retdec::common::stringToAddrRange(range);
      if (r.getStart().isUndefined() || r.getEnd().isUndefined()) {
        throw std::runtime_error("[--select-ranges] invalid range: " + range);
      }
      params.selectedRanges.insert(r);
      params.setIsKeepAllFunctions(true);
    }
  } else if (isParam(i, "", "--select-functions")) {
    std::stringstream funcs(getParamOrDie(i));
    while (funcs.good()) {
      std::string func;
      getline(funcs, func, ',');
      if (!func.empty()) {
        params.selectedFunctions.insert(func);
        params.setIsKeepAllFunctions(true);
      }
    }
  } else if (isParam(i, "", "--select-decode-only")) {
    params.setIsSelectedDecodeOnly(true);
  } else if (isParam(i, "", "--raw-section-vma")) {
    auto val = getParamOrDie(i);
    retdec::common::Address addr(val);
    if (addr.isUndefined()) {
      throw std::runtime_error("[--raw-section-vma] invalid address: " + val);
    }
    params.setSectionVMA(addr);
  } else if (isParam(i, "", "--raw-entry-point")) {
    auto val = getParamOrDie(i);
    retdec::common::Address addr(val);
    if (addr.isUndefined()) {
      throw std::runtime_error("[--raw-entry-point] invalid address: " + val);
    }
    params.setEntryPoint(addr);
  } else if (isParam(i, "", "--cleanup")) {
    cleanup = true;
  } else if (isParam(i, "", "--config")) {
    getParamOrDie(i);
    // ignore: it was already processed
  } else if (isParam(i, "", "--disable-static-code-detection")) {
    params.setIsDetectStaticCode(false);
  } else if (isParam(i, "", "--backend-disabled-opts")) {
    params.setBackendDisabledOpts(getParamOrDie(i));
  } else if (isParam(i, "", "--backend-enabled-opts")) {
    params.setBackendEnabledOpts(getParamOrDie(i));
  } else if (isParam(i, "", "--backend-call-info-obtainer")) {
    auto n = getParamOrDie(i);
    if (!(n == "optim" || n == "pessim")) {
      throw std::runtime_error("[--backend-call-info-obtainer] unknown name: " +
                               n);
    }
    params.setBackendCallInfoObtainer(n);
  } else if (isParam(i, "", "--backend-var-renamer")) {
    auto s = getParamOrDie(i);
    if (!(s == "address" || s == "hungarian" || s == "readable" ||
          s == "simple" || s == "unified")) {
      throw std::runtime_error("[--backend-var-renamer] unknown style: " + s);
    }
    params.setBackendVarRenamer(s);
  } else if (isParam(i, "", "--backend-no-opts")) {
    params.setIsBackendNoOpts(true);
  } else if (isParam(i, "", "--backend-emit-cfg")) {
    params.setIsBackendEmitCfg(true);
  } else if (isParam(i, "", "--backend-emit-cg")) {
    params.setIsBackendEmitCg(true);
  } else if (isParam(i, "", "--backend-keep-all-brackets")) {
    params.setIsBackendKeepAllBrackets(true);
  } else if (isParam(i, "", "--backend-keep-library-funcs")) {
    params.setIsBackendKeepLibraryFuncs(true);
  } else if (isParam(i, "", "--backend-no-time-varying-info")) {
    params.setIsBackendNoTimeVaryingInfo(true);
  } else if (isParam(i, "", "--backend-no-var-renaming")) {
    params.setIsBackendNoVarRenaming(true);
  } else if (isParam(i, "", "--backend-no-compound-operators")) {
    params.setIsBackendNoCompoundOperators(true);
  } else if (isParam(i, "", "--backend-no-symbolic-names")) {
    params.setIsBackendNoSymbolicNames(true);
  } else if (isParam(i, "", "--ar-index")) {
    if (!arName.empty()) {
      throw std::runtime_error(
          "[--ar-index] and [--ar-name] are mutually exclusive, "
          "use only one");
    }

    auto val = getParamOrDie(i);
    try {
      arIdx = std::stoull(val);
    } catch (...) {
      throw std::runtime_error("[--ar-index] invalid index: " + val);
    }
  } else if (isParam(i, "", "--ar-name")) {
    if (arIdx.has_value()) {
      throw std::runtime_error(
          "[--ar-name] and [--ar-index] are mutually exclusive, "
          "use only one");
    }

    arName = getParamOrDie(i);
  } else if (isParam(i, "", "--static-code-sigfile")) {
    auto file = checkFile(getParamOrDie(i), "[--static-code-sigfile]");
    params.userStaticSignaturePaths.insert(file);
  } else if (isParam(i, "", "--timeout")) {
    auto t = getParamOrDie(i);
    try {
      params.setTimeout(std::stoull(t));
    } catch (...) {
      throw std::runtime_error("[--timeout] invalid timeout value: " + t);
    }
  } else if (isParam(i, "-s", "--silent")) {
    params.setIsVerboseOutput(false);
  }
  // Input file is the only argument that does not have -x or --xyz
  // before it. But only one input is expected.
  else if (params.getInputFile().empty()) {
    params.setInputFile(c);
  } else {
    printHelpAndDie();
  }
}

/**
 * Some things can be set or checked only after all the arguments were loaded.
 */
void ProgramOptions::afterLoad() {
  auto in = params.getInputFile();
  if (params.getOutputAsmFile().empty())
    params.setOutputAsmFile(in + ".dsm");
  if (params.getOutputBitcodeFile().empty())
    params.setOutputBitcodeFile(in + ".bc");
  if (params.getOutputLlvmirFile().empty())
    params.setOutputLlvmirFile(in + ".ll");
  if (params.getOutputConfigFile().empty())
    params.setOutputConfigFile(in + ".config.json");
  if (params.getOutputFile().empty()) {
    if (params.getOutputFormat() == "plain")
      params.setOutputFile(in + ".c");
    else
      params.setOutputFile(in + ".c.json");
  }
  if (params.getOutputUnpackedFile().empty())
    params.setOutputUnpackedFile(in + "-unpacked");
  if (arExtractPath.empty())
    arExtractPath = in + "-extracted";

  if (mode == "raw") {
    if (params.getSectionVMA().isUndefined()) {
      throw std::runtime_error(
          "[--mode=raw] option --raw-section-vma must be set");
    }
    if (params.getEntryPoint().isUndefined()) {
      throw std::runtime_error(
          "[--mode=raw] option --raw-entry-point must be set");
    }
    if (config.architecture.isUnknown()) {
      throw std::runtime_error("[--mode=raw] option -a|--arch must be set");
    }
    if (config.architecture.isEndianUnknown()) {
      throw std::runtime_error("[--mode=raw] option -e|--endian must be set");
    }

    config.fileFormat.setIsRaw();
    config.fileFormat.setFileClassBits(bitSize);
    config.architecture.setBitSize(bitSize);
    params.setIsKeepAllFunctions(true);
  }

  // After everything, input file must be set.
  if (params.getInputFile().empty()) {
    throw std::runtime_error("INPUT_FILE not set");
  }
}

std::string ProgramOptions::checkFile(const std::string &path,
                                      const std::string &errorMsgPrefix) {
  if (!fs::is_regular_file(path)) {
    throw std::runtime_error(errorMsgPrefix + " bad file: " + path);
  }
  return fs::absolute(path).string();
}

void ProgramOptions::printHelpAndDie() {
  Log::info() << programName << R"(:
Mandatory arguments:
	INPUT_FILE File to decompile.
General arguments:
	[-o|--output FILE] Output file (default: INPUT_FILE.c if OUTPUT_FORMAT is plain, INPUT_FILE.c.json if OUTPUT_FORMAT is json|json-human).
	[-s|--silent] Turns off informative output of the decompilation.
	[-f|--output-format OUTPUT_FORMAT] Output format [plain|json|json-human] (default: plain).
	[-m|--mode MODE] Force the type of decompilation mode [bin|raw] (default: bin).
	[-p|--pdb FILE] File with PDB debug information.
	[-k|--keep-unreachable-funcs] Keep functions that are unreachable from the main function.
	[--cleanup] Removes temporary files created during the decompilation.
	[--config] Specify JSON decompilation configuration file.
	[--disable-static-code-detection] Prevents detection of statically linked code.
Selective decompilation arguments:
	[--select-ranges RANGES] Specify a comma separated list of ranges to decompile (example: 0x100-0x200,0x300-0x400,0x500-0x600).
	[--select-functions FUNCS] Specify a comma separated list of functions to decompile (example: fnc1,fnc2,fnc3).
	[--select-decode-only] Decode only selected parts (functions/ranges). Faster decompilation, but worse results.
Raw or Intel HEX decompilation arguments:
	[-a|--arch ARCH] Specify target architecture [mips|pic32|arm|thumb|arm64|powerpc|x86|x86-64].
	                 Required if it cannot be autodetected from the input (e.g. raw mode, Intel HEX).
	[-e|--endian ENDIAN] Specify target endianness [little|big].
	                     Required if it cannot be autodetected from the input (e.g. raw mode, Intel HEX).
	[-b|--bit-size SIZE] Specify target bit size [16|32|64] (default: 32).
	                     Required if it cannot be autodetected from the input (e.g. raw mode).
	[--raw-section-vma ADDRESS] Virtual address where section created from the raw binary will be placed.
	[--raw-entry-point ADDRESS] Entry point address used for raw binary (default: architecture dependent).
Archive decompilation arguments:
	[--ar-index INDEX] Pick file from archive for decompilation by its zero-based index.
	[--ar-name NAME] Pick file from archive for decompilation by its name.
	[--static-code-sigfile FILE] Adds additional signature file for static code detection.
Backend arguments:
	[--backend-disabled-opts LIST] Prevents the optimizations from the given comma-separated list of optimizations to be run.
	[--backend-enabled-opts LIST] Runs only the optimizations from the given comma-separated list of optimizations.
	[--backend-call-info-obtainer NAME] Name of the obtainer of information about function calls [optim|pessim] (Default: optim).
	[--backend-var-renamer STYLE] Used renamer of variables [address|hungarian|readable|simple|unified] (Default: readable).
	[--backend-no-opts] Disables backend optimizations.
	[--backend-emit-cfg] Emits a CFG for each function in the backend IR (in the .dot format).
	[--backend-emit-cg] Emits a CG for the decompiled module in the backend IR (in the .dot format).
	[--backend-keep-all-brackets] Keeps all brackets in the generated code.
	[--backend-keep-library-funcs] Keep functions from standard libraries.
	[--backend-no-time-varying-info] Do not emit time-varying information, like dates.
	[--backend-no-var-renaming] Disables renaming of variables in the backend.
	[--backend-no-compound-operators] Do not emit compound operators (like +=) instead of assignments.
	[--backend-no-symbolic-names] Disables the conversion of constant arguments to their symbolic names.
Decompilation process arguments:
	[--timeout SECONDS]
	[--max-memory MAX_MEMORY] Limits the maximal memory used by the given number of bytes.
	[--no-memory-limit] Disables the default memory limit (half of system RAM).
LLVM IR debug arguments:
	[--print-after-all] Dump LLVM IR to stderr after every LLVM pass.
	[--print-before-all] Dump LLVM IR to stderr before every LLVM pass.
Other arguments:
	[-h|--help] Show this help.
	[--version] Show RetDec version.
)";

  exit(EXIT_SUCCESS);
}

bool ProgramOptions::isParam(std::list<std::string>::iterator i,
                             const std::string &shortp,
                             const std::string &longp) {
  std::string str = *i;

  if (!shortp.empty() && retdec::utils::startsWith(str, shortp)) {
    str.erase(0, shortp.length());
    if (str.size() > 1 && str[0] == '=') {
      str.erase(0, 1);
      ++i;
      _argv.insert(i, str);
    }
    return true;
  }

  if (!longp.empty() && retdec::utils::startsWith(str, longp)) {
    str.erase(0, longp.length());
    if (str.size() > 1 && str[0] == '=') {
      str.erase(0, 1);
      ++i;
      _argv.insert(i, str);
    }
    return true;
  }

  return false;
}

std::string ProgramOptions::getParamOrDie(std::list<std::string>::iterator &i) {
  ++i;
  if (i != _argv.end()) {
    return *i;
  } else {
    printHelpAndDie();
    return std::string();
  }
}

namespace {

//
// Parameters.
//

// cl::opt<std::string> TargetHLL("target-hll",
// 	cl::desc("Name of the target HLL (set to 'help' to list all the
// supported HLLs)."), 	cl::init("!bad!"));

// cl::opt<std::string> OutputFormat("output-format",
// 	cl::desc("Output format."),
// 	cl::init("plain"));

// // We cannot use just -debug because it has been already registered :(.
// cl::opt<bool> Debug("enable-debug",
// 	cl::desc("Enables the emission of debugging messages, like information
// about the current phase."), 	cl::init(false));

// cl::opt<std::string> Semantics("semantics",
// 	cl::desc("The used semantics in the form 'sem1,sem2,...'."
// 		" When not given, the semantics is created based on the data in
// the input LLVM IR." 		" If you want to use no semantics, set this to
// 'none'."), 	cl::init(""));

// cl::opt<std::string> ConfigPath("config-path",
// 	cl::desc("Path to the configuration file."),
// 	cl::init(""));

// cl::opt<bool> EmitDebugComments("emit-debug-comments",
// 	cl::desc("Emits debugging comments in the generated code."),
// 	cl::init(false));

// cl::opt<std::string> EnabledOpts("enabled-opts",
// 	cl::desc("A comma separated list of optimizations to be enabled, i.e.
// only they will run."), 	cl::init(""));

// cl::opt<std::string> DisabledOpts("disabled-opts",
// 	cl::desc("A comma separated list of optimizations to be disabled, i.e.
// they will not run."), 	cl::init(""));

// cl::opt<bool> NoOpts("no-opts",
// 	cl::desc("Disables all optimizations."),
// 	cl::init(false));

// cl::opt<bool> AggressiveOpts("aggressive-opts",
// 	cl::desc("Enables aggressive optimizations."),
// 	cl::init(false));

// cl::opt<bool> NoVarRenaming("no-var-renaming",
// 	cl::desc("Disables renaming of variables."),
// 	cl::init(false));

// cl::opt<bool> NoSymbolicNames("no-symbolic-names",
// 	cl::desc("Disables conversion of constants into symbolic names."),
// 	cl::init(false));

// cl::opt<bool> KeepAllBrackets("keep-all-brackets",
// 	cl::desc("All brackets in the generated code will be kept."),
// 	cl::init(false));

// cl::opt<bool> KeepLibraryFunctions("keep-library-funcs",
// 	cl::desc("Functions from standard libraries will be kept, not turned
// into declarations."), 	cl::init(false));

// cl::opt<bool> NoTimeVaryingInfo("no-time-varying-info",
// 	cl::desc("Do not emit time-varying information, like dates."),
// 	cl::init(false));

// cl::opt<bool> NoCompoundOperators("no-compound-operators",
// 	cl::desc("Do not emit compound operators (like +=) instead of
// assignments."), 	cl::init(false));

// cl::opt<bool> ValidateModule("validate-module",
// 	cl::desc("Validates the resulting module before generating the target
// code."), 	cl::init(false));

// // cl::opt<std::string> FindPatterns("find-patterns",
// // 	cl::desc("If set, runs the selected comma-separated pattern finders "
// // 		"(set to 'all' to run all of them)."),
// // 	cl::init(""));

// cl::opt<std::string> AliasAnalysis("alias-analysis",
// 	cl::desc("Name of the used alias analysis "
// 		"(the default is 'simple'; set to 'help' to list all the
// supported analyses)."), 	cl::init("simple"));

// cl::opt<std::string> VarNameGen("var-name-gen",
// 	cl::desc("Name of the used generator of variable names "
// 		"(the default is 'fruit'; set to 'help' to list all the
// supported generators)."), 	cl::init("fruit"));

// cl::opt<std::string> VarNameGenPrefix("var-name-gen-prefix",
// 	cl::desc("Prefix for all variable names returned by the used generator
// of variable names "
// 		"(the default is '')."),
// 	cl::init(""));

// cl::opt<std::string> VarRenamer("var-renamer",
// 	cl::desc("Name of the used renamer of variable names "
// 		"(the default is 'readable'; set to 'help' to list all the
// supported renamers)."), 	cl::init("readable"));

// cl::opt<bool> EmitCFGs("emit-cfgs",
// 	cl::desc("Enables the emission of control-flow graphs (CFGs) for each "
// 		"function (creates a separate file for each function in the
// resulting module)."), 	cl::init(false));

// cl::opt<std::string> CFGWriter("cfg-writer",
// 	cl::desc("Name of the used CFG writer (set to 'help' to list all "
// 		"the supported writers, the default is 'dot')."),
// 	cl::init("dot"));

// cl::opt<bool> EmitCG("emit-cg",
// 	cl::desc("Emits a call graph (CG) for the decompiled module."),
// 	cl::init(false));

// cl::opt<std::string> CGWriter("cg-writer",
// 	cl::desc("Name of the used CG writer (set to 'help' to list all "
// 		"the supported writers, the default is 'dot')."),
// 	cl::init("dot"));

// cl::opt<std::string> CallInfoObtainer("call-info-obtainer",
// 	cl::desc("Name of the used obtainer of information about function calls
// (set to "
// 		"'help' to list all the supported obtainers, the default is
// 'optim')."), 	cl::init("optim"));

// cl::opt<std::string> ArithmExprEvaluator("arithm-expr-evaluator",
// 	cl::desc("Name of the used evaluator of arithmetical expressions (set to
// "
// 		"'help' to list all the supported evaluators, the default is
// 'c')."), 	cl::init("c"));

// cl::opt<std::string> ForcedModuleName("force-module-name",
// 	cl::desc("If nonempty, overwrites the module name that was
// detected/generated by the front-end. " 		"This includes the
// identifier of the input LLVM IR module as well as module names in debug
// information."), 	cl::init(""));

// cl::opt<bool> StrictFPUSemantics("strict-fpu-semantics",
// 	cl::desc("Forces strict FPU semantics to be used. "
// 		"This option may result into more correct code, although
// slightly less readable."), 	cl::init(false));

// // Does not work with std::size_t or std::uint64_t (passing -max-memory=100
// // fails with "Cannot find option named '100'!"), so we have to use unsigned
// // long long, which should be 64b.
// cl::opt<unsigned long long> MaxMemoryLimit("max-memory",
// 	cl::desc("Limit maximal memory to the given number of bytes (0 means no
// limit)."), 	cl::init(0));

// static cl::opt<bool>
// MaxMemoryLimitHalfRAM("max-memory-half-ram",
// 	cl::desc("Limit maximal memory to half of system RAM."),
// 	cl::init(false));

// cl::opt<std::string> InputFilename(cl::Positional,
// 	cl::desc("<input bitcode>"),
// 	cl::init("-"));

// cl::opt<std::string> OutputFilename("o",
// 	cl::desc("Output filename"),
// 	cl::value_desc("filename"));

/**
 * @brief Returns a list of all supported objects by the given factory.
 *
 * @tparam FactoryType Type of the factory in whose objects we are interested
 * in.
 *
 * The list is comma separated and has no beginning or trailing whitespace.
 */
template <typename FactoryType> std::string getListOfSupportedObjects() {
  return joinStrings(FactoryType::getInstance().getRegisteredObjects());
}

/**
 * @brief Prints an error message concerning the situation when an unsupported
 *        object has been selected from the given factory.
 *
 * @param[in] typeOfObjectsSingular A human-readable description of the type of
 *                                  objects the factory provides. In the
 *                                  singular form, e.g. "HLL writer".
 * @param[in] typeOfObjectsPlural A human-readable description of the type of
 *                                objects the factory provides. In the plural
 *                                form, e.g. "HLL writers".
 *
 * @tparam FactoryType Type of the factory in whose objects we are interested
 * in.
 */
template <typename FactoryType>
void printErrorUnsupportedObject(const std::string &typeOfObjectsSingular,
                                 const std::string &typeOfObjectsPlural) {
  std::string supportedObjects(getListOfSupportedObjects<FactoryType>());
  if (!supportedObjects.empty()) {
    std::cerr << "Invalid name of the " << typeOfObjectsSingular
              << " (supported names are: " << supportedObjects << ")."
              << std::endl;
    throw std::runtime_error("");
  } else {
    std::cerr << "There are no available " << typeOfObjectsPlural
              << ". Please, recompile the backend and try it"
                 " again."
              << std::endl;
    throw std::runtime_error("");
  }
}

} // anonymous namespace

// namespace llvmir2hlltool {

// /**
// * @brief This class is the main chunk of code that converts an LLVM
// *        module to the specified high-level language (HLL).
// *
// * The decompilation is composed of the following steps:
// * 1) LLVM instantiates Decompiler with the output stream, where the target
// *    code will be emitted.
// * 2) The function runOnModule() is called, which decompiles the given
// *    LLVM IR into BIR (backend IR).
// * 3) The resulting IR is then converted into the requested HLL at the end of
// *    runOnModule().
// *
// * The HLL is specified in `-target-hll` when running llvmir2hll. Debug
// comments
// * can be enabled by using the `-emit-debug-comments` parameter. For more
// * information, run llvmir2hll with `-help`.
// */
// class Decompiler: public ModulePass {
// public:
// 	explicit Decompiler(raw_pwrite_stream &out);

// 	virtual llvm::StringRef getPassName() const override { return
// "Decompiler"; } 	virtual bool runOnModule(Module &m) override;

// public:
// 	/// Class identification.
// 	static char ID;

// private:
// 	virtual void getAnalysisUsage(AnalysisUsage &au) const override {
// 		au.addRequired<LoopInfoWrapperPass>();
// 		au.addRequired<ScalarEvolutionWrapperPass>();
// 		au.setPreservesAll();
// 	}

// 	bool initialize(Module &m);
// 	bool limitMaximalMemoryIfRequested();
// 	void createSemantics();
// 	void createSemanticsFromParameter();
// 	void createSemanticsFromLLVMIR();
// 	bool loadConfig();
// 	void saveConfig();
// 	bool convertLLVMIRToBIR();
// 	void removeLibraryFuncs();
// 	void removeCodeUnreachableInCFG();
// 	// void removeFuncsPrefixedWith(const retdec::llvmir2hll::StringSet
// &prefixes); 	void fixSignedUnsignedTypes(); 	void
// convertLLVMIntrinsicFunctions(); 	void obtainDebugInfo(); 	void
// initAliasAnalysis(); 	void runOptimizations(); 	void
// renameVariables(); 	void convertConstantsToSymbolicNames(); 	void
// validateResultingModule();
// 	// void findPatterns();
// 	void emitCFGs();
// 	void emitCG();
// 	void emitTargetHLLCode();
// 	void finalize();
// 	void cleanup();

// 	retdec::llvmir2hll::StringSet parseListOfOpts(const std::string &opts)
// const; 	std::string getTypeOfRunOptimizations() const;
// 	// retdec::llvmir2hll::StringVector getIdsOfPatternFindersToBeRun()
// const; 	retdec::llvmir2hll::PatternFinderRunner::PatternFinders
// instantiatePatternFinders( 		const retdec::llvmir2hll::StringVector
// &pfsIds);
// 	// ShPtr<retdec::llvmir2hll::PatternFinderRunner>
// instantiatePatternFinderRunner() const;
// 	// retdec::llvmir2hll::StringSet getPrefixesOfFuncsToBeRemoved() const;

// private:
// 	/// Output stream into which the generated code will be emitted.
// 	raw_pwrite_stream &out;

// 	/// The input LLVM module.
// 	Module *llvmModule;

// 	/// The resulting module in BIR.
// 	ShPtr<retdec::llvmir2hll::Module> resModule;

// 	/// The used semantics.
// 	ShPtr<retdec::llvmir2hll::Semantics> semantics;

// 	/// The used config.
// 	ShPtr<retdec::llvmir2hll::Config> config;

// 	/// The used HLL writer.
// 	ShPtr<retdec::llvmir2hll::HLLWriter> hllWriter;

// 	/// The used alias analysis.
// 	ShPtr<retdec::llvmir2hll::AliasAnalysis> aliasAnalysis;

// 	/// The used obtainer of information about function and function calls.
// 	ShPtr<retdec::llvmir2hll::CallInfoObtainer> cio;

// 	/// The used evaluator of arithmetical expressions.
// 	ShPtr<retdec::llvmir2hll::ArithmExprEvaluator> arithmExprEvaluator;

// 	/// The used generator of variable names.
// 	ShPtr<retdec::llvmir2hll::VarNameGen> varNameGen;

// 	/// The used renamer of variables.
// 	ShPtr<retdec::llvmir2hll::VarRenamer> varRenamer;
// };

// // Static variables and constants initialization.
// char Decompiler::ID = 0;

// /**
// * @brief Constructs a new decompiler.
// *
// * @param[in] out Output stream into which the generated HLL code will be
// *                emitted.
// */
// Decompiler::Decompiler(raw_pwrite_stream &out):
// 	ModulePass(ID), out(out), llvmModule(nullptr), resModule(), semantics(),
// 	hllWriter(), aliasAnalysis(), cio(), arithmExprEvaluator(),
// 	varNameGen(), varRenamer() {}

// bool Decompiler::runOnModule(Module &m) {
// 	if (Debug) std::cout << "Phase: " << "initialization" << std::endl;

// 	bool decompilationShouldContinue = initialize(m);
// 	if (!decompilationShouldContinue) {
// 		return false;
// 	}

// 	if (Debug) std::cout << "Phase: " << "conversion of LLVM IR into BIR" <<
// std::endl; 	decompilationShouldContinue = convertLLVMIRToBIR(); 	if
// (!decompilationShouldContinue) { 		return false;
// 	}

// 	// retdec::llvmir2hll::StringSet
// funcPrefixes(getPrefixesOfFuncsToBeRemoved());
// 	// if (Debug) std::cout << "Phase: " << "removing functions prefixed
// with [" + joinStrings(funcPrefixes) + "]" << std::endl;
// 	// removeFuncsPrefixedWith(funcPrefixes);

// 	// if (!KeepLibraryFunctions) {
// 	// 	if (Debug) std::cout << "Phase: " << "removing functions from
// standard libraries" << std::endl;
// 	// 	removeLibraryFuncs();
// 	// }

// 	// The following phase needs to be done right after the conversion
// because
// 	// there may be code that is not reachable in a CFG. This happens
// because
// 	// the conversion of LLVM IR to BIR is not perfect, so it may introduce
// 	// unreachable code. This causes problems later during optimizations
// 	// because the code exists in BIR, but not in a CFG.
// 	if (Debug) std::cout << "Phase: " << "removing code that is not
// reachable in a CFG" << std::endl; 	removeCodeUnreachableInCFG();

// 	if (Debug) std::cout << "Phase: " << "signed/unsigned types fixing" <<
// std::endl; 	fixSignedUnsignedTypes();

// 	if (Debug) std::cout << "Phase: " << "converting LLVM intrinsic
// functions to standard functions" << std::endl;
// 	convertLLVMIntrinsicFunctions();

// 	if (resModule->isDebugInfoAvailable()) {
// 		if (Debug) std::cout << "Phase: " << "obtaining debug
// information"
// << std::endl; 		obtainDebugInfo();
// 	}

// 	// if (!NoOpts) {
// 	// 	if (Debug) std::cout << "Phase: " << "alias analysis [" +
// aliasAnalysis->getId() + "]" << std::endl;
// 	// 	initAliasAnalysis();

// 	// 	// if (Debug) std::cout << "Phase: " << "optimizations [" +
// getTypeOfRunOptimizations() + "]" << std::endl;
// 	// 	// runOptimizations();
// 	// }

// 	// if (!NoVarRenaming) {
// 	// 	if (Debug) std::cout << "Phase: " << "variable renaming [" +
// varRenamer->getId() + "]" << std::endl;
// 	// 	renameVariables();
// 	// }

// 	// if (!NoSymbolicNames) {
// 	// 	if (Debug) std::cout << "Phase: " << "converting constants to
// symbolic names" << std::endl;
// 	// 	convertConstantsToSymbolicNames();
// 	// }

// 	// if (ValidateModule) {
// 	// 	if (Debug) std::cout << "Phase: " << "module validation" <<
// std::endl;
// 	// 	validateResultingModule();
// 	// }

// 	// // if (!FindPatterns.empty()) {
// 	// // 	if (Debug) std::cout << "Phase: " << "finding patterns" <<
// std::endl;
// 	// // 	findPatterns();
// 	// // }

// 	// if (EmitCFGs) {
// 	// 	if (Debug) std::cout << "Phase: " << "emission of control-flow
// graphs" << std::endl;
// 	// 	emitCFGs();
// 	// }

// 	// if (EmitCG) {
// 	// 	if (Debug) std::cout << "Phase: " << "emission of a call graph"
// << std::endl;
// 	// 	emitCG();
// 	// }

// 	if (Debug) std::cout << "Phase: " << "emission of the target code [" +
// hllWriter->getId() + "]" << std::endl; 	emitTargetHLLCode();

// 	if (Debug) std::cout << "Phase: " << "finalization" << std::endl;
// 	finalize();

// 	if (Debug) std::cout << "Phase: " << "cleanup" << std::endl;
// 	cleanup();

// 	return false;
// }

// /**
// * @brief Initializes all the needed private variables.
// *
// * @return @c true if the decompilation should continue (the initialization
// went
// *         OK), @c false otherwise.
// */
// bool Decompiler::initialize(Module &m) {
// 	llvmModule = &m;

// 	// Maximal memory limitation.
// 	bool memoryLimitationSucceeded = limitMaximalMemoryIfRequested();
// 	if (!memoryLimitationSucceeded) {
// 		return false;
// 	}

// 	// // Instantiate the requested HLL writer and make sure it exists. We
// need to
// 	// // explicitly specify template parameters because raw_pwrite_stream
// has
// 	// // a private copy constructor, so it needs to be passed by reference.
// 	// if (Debug) std::cout << "SubPhase: " << "creating the used HLL writer
// [" + TargetHLL + "]" << std::endl;
// 	// hllWriter =
// retdec::llvmir2hll::HLLWriterFactory::getInstance().createObject<
// 	// 	raw_pwrite_stream &>(TargetHLL, out, OutputFormat);
// 	// if (!hllWriter) {
// 	//
// printErrorUnsupportedObject<retdec::llvmir2hll::HLLWriterFactory>(
// 	// 		"target HLL", "target HLLs");
// 	// 	return false;
// 	// }

// 	// // Instantiate the requested alias analysis and make sure it exists.
// 	// if (Debug) std::cout << "SubPhase: " << "creating the used alias
// analysis [" + AliasAnalysis + "]" << std::endl;
// 	// aliasAnalysis =
// retdec::llvmir2hll::AliasAnalysisFactory::getInstance().createObject(
// 	// 	AliasAnalysis);
// 	// if (!aliasAnalysis) {
// 	//
// printErrorUnsupportedObject<retdec::llvmir2hll::AliasAnalysisFactory>(
// 	// 		"alias analysis", "alias analyses");
// 	// 	return false;
// 	// }

// 	// // Instantiate the requested obtainer of information about function
// 	// // calls and make sure it exists.
// 	// if (Debug) std::cout << "SubPhase: " << "creating the used call info
// obtainer [" + CallInfoObtainer + "]" << std::endl;
// 	// cio =
// retdec::llvmir2hll::CallInfoObtainerFactory::getInstance().createObject(
// 	// 	CallInfoObtainer);
// 	// if (!cio) {
// 	//
// printErrorUnsupportedObject<retdec::llvmir2hll::CallInfoObtainerFactory>(
// 	// 		"call info obtainer", "call info obtainers");
// 	// 	return false;
// 	// }

// 	// // Instantiate the requested evaluator of arithmetical expressions
// and make
// 	// // sure it exists.
// 	// if (Debug) std::cout << "SubPhase: " << "creating the used evaluator
// of arithmetical expressions [" +
// 	// 	ArithmExprEvaluator + "]";
// 	// arithmExprEvaluator =
// retdec::llvmir2hll::ArithmExprEvaluatorFactory::getInstance().createObject(
// 	// 	ArithmExprEvaluator);
// 	// if (!arithmExprEvaluator) {
// 	//
// printErrorUnsupportedObject<retdec::llvmir2hll::ArithmExprEvaluatorFactory>(
// 	// 		"evaluator of arithmetical expressions", "evaluators of
// arithmetical expressions");
// 	// 	return false;
// 	// }

// 	// // Instantiate the requested variable names generator and make sure
// it
// 	// // exists.
// 	// if (Debug) std::cout << "SubPhase: " << "creating the used variable
// names generator [" + VarNameGen + "]" << std::endl;
// 	// varNameGen =
// retdec::llvmir2hll::VarNameGenFactory::getInstance().createObject(
// 	// 	VarNameGen, VarNameGenPrefix);
// 	// if (!varNameGen) {
// 	//
// printErrorUnsupportedObject<retdec::llvmir2hll::VarNameGenFactory>(
// 	// 		"variable names generator", "variable names
// generators");
// 	// 	return false;
// 	// }

// 	// // Instantiate the requested variable renamer and make sure it
// exists.
// 	// if (Debug) std::cout << "SubPhase: " << "creating the used variable
// renamer [" + VarRenamer + "]" << std::endl;
// 	// varRenamer =
// retdec::llvmir2hll::VarRenamerFactory::getInstance().createObject(
// 	// 	VarRenamer, varNameGen, true);
// 	// if (!varRenamer) {
// 	//
// printErrorUnsupportedObject<retdec::llvmir2hll::VarRenamerFactory>(
// 	// 		"renamer of variables", "renamers of variables");
// 	// 	return false;
// 	// }

// 	createSemantics();

// 	bool configLoaded = loadConfig();
// 	if (!configLoaded) {
// 		return false;
// 	}

// 	// Everything went OK.
// 	return true;
// }

// // /**
// // * @brief Limits the maximal memory of the tool based on the command-line
// // *        parameters.
// // */
// // bool Decompiler::limitMaximalMemoryIfRequested() {
// // 	if (MaxMemoryLimitHalfRAM) {
// // 		auto limitationSucceeded =
// limitSystemMemoryToHalfOfTotalSystemMemory();
// // 		if (!limitationSucceeded) {
// // 			std::cerr <<
// // 				"Failed to limit maximal memory to half of
// system RAM." << std::endl;
// // 			return false;
// // 		}
// // 	} else if (MaxMemoryLimit > 0) {
// // 		auto limitationSucceeded = limitSystemMemory(MaxMemoryLimit);
// // 		if (!limitationSucceeded) {
// // 			std::cerr <<
// // 				"Failed to limit maximal memory to " +
// std::to_string(MaxMemoryLimit) + "." << std::endl;
// // 		}
// // 	}

// // 	return true;
// // }

// // /**
// // * @brief Creates the used semantics.
// // */
// // void Decompiler::createSemantics() {
// // 	if (!Semantics.empty()) {
// // 		// The user has requested some concrete semantics, so use it.
// // 		createSemanticsFromParameter();
// // 	} else {
// // 		// The user didn't request any semantics, so create it based on
// the
// // 		// data in the input LLVM IR.
// // 		createSemanticsFromLLVMIR();
// // 	}
// // }

// // /**
// // * @brief Creates the used semantics as requested by the user.
// // */
// // void Decompiler::createSemanticsFromParameter() {
// // 	if (Semantics.empty() || Semantics == "-") {
// // 		// Do no use any semantics.
// // 		if (Debug) std::cout << "SubPhase: " << "creating the used
// semantics [none]" << std::endl;
// // 		semantics = retdec::llvmir2hll::DefaultSemantics::create();
// // 	} else {
// // 		// Use the given semantics.
// // 		if (Debug) std::cout << "SubPhase: " << "creating the used
// semantics [" + Semantics + "]" << std::endl;
// // 		semantics =
// retdec::llvmir2hll::CompoundSemanticsBuilder::build(split(Semantics, ','));
// // 	}
// // }

// // /**
// // * @brief Creates the used semantics based on the data in the input LLVM
// IR.
// // */
// // void Decompiler::createSemanticsFromLLVMIR() {
// // 	// Create a list of the semantics to be used.
// // 	// TODO Use some data from the input LLVM IR, like the used compiler.
// // 	std::string usedSemantics("libc,gcc-general,win-api");

// // 	// Use the list to create the semantics.
// // 	if (Debug) std::cout << "SubPhase: " << "creating the used semantics ["
// + usedSemantics + "]" << std::endl;
// // 	semantics =
// retdec::llvmir2hll::CompoundSemanticsBuilder::build(split(usedSemantics,
// ','));
// // }

// // /**
// // * @brief Loads a config for the module.
// // *
// // * @return @a true if the config was loaded successfully, @c false
// otherwise.
// // */
// // bool Decompiler::loadConfig() {
// // 	// Currently, we always use the JSON config.
// // 	if (ConfigPath.empty()) {
// // 		if (Debug) std::cout << "SubPhase: " << "creating a new config"
// << std::endl;
// // 		config = retdec::llvmir2hll::JSONConfig::empty();
// // 		return true;
// // 	}

// // 	if (Debug) std::cout << "SubPhase: " << "loading the input config" <<
// std::endl;
// // 	try {
// // 		config = retdec::llvmir2hll::JSONConfig::fromFile(ConfigPath);
// // 		return true;
// // 	} catch (const retdec::llvmir2hll::ConfigError &ex) {
// // 		std::cerr <<
// // 			"Loading of the config failed: " + ex.getMessage() + "."
// << std::endl;
// // 		return false;
// // 	}
// // }

// // /**
// // * @brief Saves the config file.
// // */
// // void Decompiler::saveConfig() {
// // 	if (!ConfigPath.empty()) {
// // 		config->saveTo(ConfigPath);
// // 	}
// // }

// // /**
// // * @brief Convert the LLVM IR module into a BIR module using the
// instantiated
// // *        converter.
// // * @return @c True if decompilation should continue, @c False if something
// went
// // *         wrong and decompilation should abort.
// // */
// // bool Decompiler::convertLLVMIRToBIR() {
// // 	auto llvm2BIRConverter =
// retdec::llvmir2hll::LLVMIR2BIRConverter::create(this);
// // 	// Options
// // 	llvm2BIRConverter->setOptionStrictFPUSemantics(StrictFPUSemantics);

// // 	std::string moduleName = ForcedModuleName.empty() ?
// // 		llvmModule->getModuleIdentifier() : ForcedModuleName;
// // 	resModule = llvm2BIRConverter->convert(llvmModule, moduleName,
// // 		semantics, config, Debug);

// // 	return true;
// // }

// // /**
// // * @brief Removes defined functions which are from some standard library
// whose
// // *        header file has to be included because of some function
// declarations.
// // */
// // void Decompiler::removeLibraryFuncs() {
// // 	retdec::llvmir2hll::FuncVector
// removedFuncs(retdec::llvmir2hll::LibraryFuncsRemover::removeFuncs(
// // 		resModule));

// // 	if (Debug) {
// // 		// Emit the functions that were turned into declarations. Before
// that,
// // 		// however, sort them by name to provide a more deterministic
// output.
// // 		retdec::llvmir2hll::sortByName(removedFuncs);
// // 		for (const auto &func : removedFuncs) {
// // 			std::cout << "SubPhase: " << "removing " +
// func->getName()
// + "()" << std::endl;
// // 		}
// // 	}
// // }

// // /**
// // * @brief Removes code from all the functions in the module that is
// unreachable
// // *        in the CFG.
// // */
// // void Decompiler::removeCodeUnreachableInCFG() {
// // 	retdec::llvmir2hll::UnreachableCodeInCFGRemover::removeCode(resModule);
// // }

// // // /**
// // // * @brief Removes functions with the given prefix.
// // // */
// // // void Decompiler::removeFuncsPrefixedWith(const
// retdec::llvmir2hll::StringSet &prefixes) {
// // //
// retdec::llvmir2hll::FuncsWithPrefixRemover::removeFuncs(resModule, prefixes);
// // // }

// // /**
// // * @brief Fixes signed and unsigned types in the resulting module.
// // */
// // void Decompiler::fixSignedUnsignedTypes() {
// // 	retdec::llvmir2hll::ExprTypesFixer::fixTypes(resModule);
// // }

// // /**
// // * @brief Converts LLVM intrinsic functions to functions from the standard
// // *        library.
// // */
// // void Decompiler::convertLLVMIntrinsicFunctions() {
// // 	retdec::llvmir2hll::LLVMIntrinsicConverter::convert(resModule);
// // }

// // /**
// // * @brief When available, obtains debugging information.
// // */
// // void Decompiler::obtainDebugInfo() {
// // 	retdec::llvmir2hll::LLVMDebugInfoObtainer::obtainVarNames(resModule);
// // }

// // /**
// // * @brief Initializes the alias analysis.
// // */
// // void Decompiler::initAliasAnalysis() {
// // 	aliasAnalysis->init(resModule);
// // }

// // /**
// // * @brief Runs the optimizations over the resulting module.
// // */
// // // void Decompiler::runOptimizations() {
// // // 	ShPtr<retdec::llvmir2hll::OptimizerManager> optManager(new
// retdec::llvmir2hll::OptimizerManager(
// // // 		parseListOfOpts(EnabledOpts),
// parseListOfOpts(DisabledOpts),
// // // 		hllWriter,
// retdec::llvmir2hll::ValueAnalysis::create(aliasAnalysis, true), cio,
// // // 		arithmExprEvaluator, AggressiveOpts, Debug));
// // // 	optManager->optimize(resModule);
// // // }

// // /**
// // * @brief Renames variables in the resulting module by using the selected
// // *        variable renamer.
// // */
// // void Decompiler::renameVariables() {
// // 	varRenamer->renameVars(resModule);
// // }

// // /**
// // * @brief Converts constants in function calls to symbolic names.
// // */
// // void Decompiler::convertConstantsToSymbolicNames() {
// // 	retdec::llvmir2hll::ConstSymbolConverter::convert(resModule);
// // }

// // /**
// // * @brief Validates the resulting module.
// // */
// // void Decompiler::validateResultingModule() {
// // 	// Run all the registered validators over the resulting module, sorted
// by
// // 	// name.
// // 	retdec::llvmir2hll::StringVector regValidatorIDs(
// //
// retdec::llvmir2hll::ValidatorFactory::getInstance().getRegisteredObjects());
// // 	std::sort(regValidatorIDs.begin(), regValidatorIDs.end());
// // 	for (const auto &id : regValidatorIDs) {
// // 		if (Debug) std::cout << "SubPhase: " << "running " + id +
// "Validator" << std::endl;
// // 		ShPtr<retdec::llvmir2hll::Validator> validator(
// //
// retdec::llvmir2hll::ValidatorFactory::getInstance().createObject(id));
// // 		validator->validate(resModule, true);
// // 	}
// // }

// // // /**
// // // * @brief Finds patterns in the resulting module.
// // // */
// // // void Decompiler::findPatterns() {
// // // 	retdec::llvmir2hll::StringVector
// pfsIds(getIdsOfPatternFindersToBeRun());
// // // 	retdec::llvmir2hll::PatternFinderRunner::PatternFinders
// pfs(instantiatePatternFinders(pfsIds));
// // // 	ShPtr<retdec::llvmir2hll::PatternFinderRunner>
// pfr(instantiatePatternFinderRunner());
// // // 	pfr->run(pfs, resModule);
// // // }

// // /**
// // * @brief Emits the target HLL code.
// // */
// // void Decompiler::emitTargetHLLCode() {
// // 	hllWriter->setOptionEmitDebugComments(EmitDebugComments);
// // 	hllWriter->setOptionKeepAllBrackets(KeepAllBrackets);
// // 	hllWriter->setOptionEmitTimeVaryingInfo(!NoTimeVaryingInfo);
// // 	hllWriter->setOptionUseCompoundOperators(!NoCompoundOperators);
// // 	hllWriter->emitTargetCode(resModule);
// // }

// // /**
// // * @brief Finalizes the run of the back-end part.
// // */
// // void Decompiler::finalize() {
// // 	saveConfig();
// // }

// // /**
// // * @brief Cleanup.
// // */
// // void Decompiler::cleanup() {
// // 	// Nothing to do.

// // 	// Note: Do not remove this phase, even if there is nothing to do. The
// // 	// presence of this phase is needed for the analyzing scripts in
// // 	// scripts/decompiler_tests (it marks the very last phase of a
// successful
// // 	// decompilation).
// // }

// // /**
// // * @brief Emits a control-flow graph (CFG) for each function in the
// resulting
// // *        module.
// // */
// // void Decompiler::emitCFGs() {
// // 	// Make sure that the requested CFG writer exists.
// // 	retdec::llvmir2hll::StringVector availCFGWriters(
// //
// retdec::llvmir2hll::CFGWriterFactory::getInstance().getRegisteredObjects());
// // 	if (!hasItem(availCFGWriters, std::string(CFGWriter))) {
// // printErrorUnsupportedObject<retdec::llvmir2hll::CFGWriterFactory>(
// // 			"CFG writer", "CFG writers");
// // 		return;
// // 	}

// // 	// Instantiate a CFG builder.
// // 	ShPtr<retdec::llvmir2hll::CFGBuilder>
// cfgBuilder(retdec::llvmir2hll::NonRecursiveCFGBuilder::create());

// // 	// Get the extension of the files that will be written (we use the CFG
// // 	// writer's name for this purpose).
// // 	std::string fileExt(CFGWriter);

// // 	// For each function in the resulting module...
// // 	for (auto i = resModule->func_definition_begin(),
// // 			e = resModule->func_definition_end(); i != e; ++i) {
// // 		// Open the output file.
// // 		std::string fileName(OutputFilename + ".cfg." + (*i)->getName()
// + "." + fileExt);
// // 		std::ofstream out(fileName.c_str());
// // 		if (!out) {
// // 			std::cerr << "Cannot open " + fileName + " for writing."
// << std::endl;
// // 			return;
// // 		}
// // 		// Create a CFG for the current function and emit it into the
// opened
// // 		// file.
// // 		ShPtr<retdec::llvmir2hll::CFGWriter>
// writer(retdec::llvmir2hll::CFGWriterFactory::getInstance(
// // 			).createObject<ShPtr<retdec::llvmir2hll::CFG>,
// std::ostream
// &>(
// // 				CFGWriter, cfgBuilder->getCFG(*i), out));
// // 		ASSERT_MSG(writer, "instantiation of the requested CFG writer `"
// // 			<< CFGWriter << "` failed");
// // 		writer->emitCFG();
// // 	}
// // }

// // /**
// // * @brief Emits a call graph (CG) for the resulting module.
// // */
// // void Decompiler::emitCG() {
// // 	// Make sure that the requested CG writer exists.
// // 	retdec::llvmir2hll::StringVector availCGWriters(
// //
// retdec::llvmir2hll::CGWriterFactory::getInstance().getRegisteredObjects());
// // 	if (!hasItem(availCGWriters, std::string(CGWriter))) {
// // printErrorUnsupportedObject<retdec::llvmir2hll::CGWriterFactory>(
// // 			"CG writer", "CG writers");
// // 		return;
// // 	}

// // 	// Get the extension of the file that will be written (we use the CG
// // 	// writer's name for this purpose).
// // 	std::string fileExt(CGWriter);

// // 	// Open the output file.
// // 	std::string fileName(OutputFilename + ".cg." + fileExt);
// // 	std::ofstream out(fileName.c_str());
// // 	if (!out) {
// // 		std::cerr << "Cannot open " + fileName + " for writing." <<
// std::endl;
// // 		return;
// // 	}

// // 	// Create a CG for the current module and emit it into the opened file.
// // 	ShPtr<retdec::llvmir2hll::CGWriter>
// writer(retdec::llvmir2hll::CGWriterFactory::getInstance(
// // 		).createObject<ShPtr<retdec::llvmir2hll::CG>, std::ostream &>(
// // 			CGWriter,
// retdec::llvmir2hll::CGBuilder::getCG(resModule), out));
// // 	ASSERT_MSG(writer,
// // 		"instantiation of the requested CG writer `" << CGWriter << "`
// failed");
// // 	writer->emitCG();
// // }

// // /**
// // * @brief Parses the given list of optimizations.
// // *
// // * @a opts should be a list of strings separated by a comma.
// // */
// // retdec::llvmir2hll::StringSet Decompiler::parseListOfOpts(const
// std::string &opts) const {
// // 	retdec::llvmir2hll::StringVector parsedOpts(split(opts, ','));
// // 	return retdec::llvmir2hll::StringSet(parsedOpts.begin(),
// parsedOpts.end());
// // }

// // /**
// // * @brief Returns the type of optimizations that should be run (as a
// string).
// // */
// // std::string Decompiler::getTypeOfRunOptimizations() const {
// // 	return AggressiveOpts ? "aggressive" : "normal";
// // }

// // /**
// // * @brief Returns the IDs of pattern finders to be run.
// // */
// // retdec::llvmir2hll::StringVector
// Decompiler::getIdsOfPatternFindersToBeRun() const {
// // 	if (FindPatterns == "all") {
// // 		// Get all of them.
// // 		return
// retdec::llvmir2hll::PatternFinderFactory::getInstance().getRegisteredObjects();
// // 	} else {
// // 		// Get only the selected IDs.
// // 		return split(FindPatterns, ',');
// // 	}
// // }

// // /**
// // * @brief Instantiates and returns a proper PatternFinderRunner.
// // */
// // ShPtr<retdec::llvmir2hll::PatternFinderRunner>
// Decompiler::instantiatePatternFinderRunner() const {
// // 	if (Debug) {
// // 		return ShPtr<retdec::llvmir2hll::PatternFinderRunner>(new
// retdec::llvmir2hll::CLIPatternFinderRunner(llvm::errs()));
// // 	}
// // 	return ShPtr<retdec::llvmir2hll::PatternFinderRunner>(new
// retdec::llvmir2hll::NoActionPatternFinderRunner());
// // }

// // /**
// // * @brief Returns the prefixes of functions to be removed.
// // */
// // retdec::llvmir2hll::StringSet Decompiler::getPrefixesOfFuncsToBeRemoved()
// const {
// // 	return config->getPrefixesOfFuncsToBeRemoved();
// // }

// //
// // External interface
// //

// class DecompilerTargetMachine: public TargetMachine {
// public:
// 	DecompilerTargetMachine(const Target &t, StringRef dataLayoutString,
// 		const Triple &targetTriple, StringRef cpu, StringRef fs,
// 		const TargetOptions &options):
// 			TargetMachine(t, dataLayoutString, targetTriple, cpu,
// fs, options) {}

// 	virtual bool addPassesToEmitFile(
// 			PassManagerBase &pm,
// 			raw_pwrite_stream &out,
// 			raw_pwrite_stream *,
// 			CodeGenFileType fileType,
// 			bool disableVerify = true,
// 			MachineModuleInfo *MMI = nullptr) override;
// };

// bool DecompilerTargetMachine::addPassesToEmitFile(
// 		PassManagerBase &pm,
// 		raw_pwrite_stream &out,
// 		raw_pwrite_stream *,
// 		CodeGenFileType fileType,
// 		bool disableVerify,
// 		MachineModuleInfo *MMI) {
// 	if (fileType != TargetMachine::CGFT_AssemblyFile) {
// 		return true;
// 	}

// 	// Add and initialize all required passes to perform the decompilation.
// 	pm.add(new LoopInfoWrapperPass());
// 	pm.add(new ScalarEvolutionWrapperPass());
// 	pm.add(new Decompiler(out));

// 	return false;
// }

// } // namespace llvmir2hlltool

//
// llvm/tools/llc/llc.cpp
//

namespace {

// Target decompilerTarget;

std::unique_ptr<llvm::ToolOutputFile>
getOutputStream(const std::string &outputFile) {
  // Open the file.
  std::error_code ec;
  auto out = std::make_unique<ToolOutputFile>(outputFile, ec, sys::fs::OF_None);
  if (ec) {
    Log::error() << ec.message() << '\n';
    return {};
  }
  if (out)
    out->keep();
  return out;
}

/**
 * Call a bunch of LLVM initialization functions, same as the original opt.
 */
llvm::PassRegistry &initializeLlvmPasses() {
  // Initialize passes
  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  initializeCore(Registry);
  initializeScalarOpts(Registry);
  initializeIPO(Registry);
  initializeAnalysis(Registry);
  initializeTransformUtils(Registry);
  initializeInstCombine(Registry);
  initializeTarget(Registry);
  return Registry;
}

/**
 * This pass just prints phase information about other, subsequent passes.
 * In pass manager, tt should be placed right before the pass which phase info
 * it is printing.
 */
class ModulePassPrinter : public ModulePass {
public:
  static char ID;
  std::string PhaseName;
  std::string PhaseArg;
  std::string PassName;

  static std::string LastPhase;
  inline static const std::string LlvmAggregatePhaseName = "LLVM";

public:
  ModulePassPrinter(const std::string &phaseName, const std::string &phaseArg)
      : ModulePass(ID), PhaseName(phaseName), PhaseArg(phaseArg),
        PassName("ModulePass Printer: " + PhaseName) {}

  bool runOnModule(Module &M) override {
    if (retdec::utils::startsWith(PhaseArg, "retdec")) {
      Log::phase(PhaseName);
      LastPhase = PhaseArg;
    } else {
      // aggregate LLVM
      if (LastPhase != LlvmAggregatePhaseName) {
        Log::phase(LlvmAggregatePhaseName);
        LastPhase = LlvmAggregatePhaseName;
      }

      // print all
      // Log::phase(PhaseName);
      // LastPhase = PhaseArg;
    }
    return false;
  }

  llvm::StringRef getPassName() const override { return PassName.c_str(); }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }
};
char ModulePassPrinter::ID = 0;
std::string ModulePassPrinter::LastPhase;

/**
 * Add the pass to the pass manager - no verification.
 */
static inline void addPass(legacy::PassManagerBase &PM, Pass *P,
                           const PassInfo *PI) {
  PM.add(new ModulePassPrinter(PI->getPassName().str(),
                               PI->getPassArgument().str()));
  PM.add(P);

  // if (!PI->isAnalysis())
  // PM.add(P->createPrinterPass(
  // 		dbgs(),
  // 		("*** IR Dump After " + P->getPassName() + " ***").str()
  // ));
}

int compileModule(retdec::config::Config &config) {
  auto context = std::make_unique<llvm::LLVMContext>();

  // Load the module to be compiled.
  SMDiagnostic err;
  std::unique_ptr<Module> module(
      parseIRFile(config.parameters.getInputFile(), err, *context));
  if (!module) {
    Log::error() << "Failed to load IR.\n";
    err.print("program", llvm::errs());
    return 1;
  }

  // If we are supposed to override the target triple, do so now.
  // Triple triple(module->getTargetTriple());
  // if (triple.getTriple().empty()) {
  // 	triple.setTriple("wasm32-unknown-wasi");
  // }

  // Get the target-specific parser.
  // auto target =
  // std::make_unique<retdec::llvmir2hlltool::DecompilerTargetMachine>(
  // 	decompilerTarget, "", triple, "", "", TargetOptions()
  // );
  // assert(target && "Could not allocate target machine!");

  // Figure out where we are going to send the output.
  // auto out = getOutputStream(config.parameters.getOutputFile());
  // if (!out) {
  // 	Log::error() << "Failed to create ToolOutputFile.";
  // 	return 1;
  // }

  // add Config
  // retdec::bin2llvmir::ConfigProvider::addConfig(module.get(), config);

  // // provider-init
  // config.parameters.setEntryPoint(retdec::common::Address(0) );
  // config.parameters.setMainAddress(retdec::common::Address(0) );
  // config.parameters.setSectionVMA(retdec::common::Address(0));
  // config.architecture.setIsWasm();
  // config.architecture.setIsEndianLittle();
  // config.architecture.setBitSize(32);

  // bin2llvmir config
  // retdec::bin2llvmir::Config* c =
  // retdec::bin2llvmir::ConfigProvider::addConfig(module.get(), config); auto*
  // abi = retdec::bin2llvmir::AbiProvider::addAbi(module.get(), c);
  // retdec::bin2llvmir::SymbolicTree::setAbi(abi);
  // retdec::bin2llvmir::SymbolicTree::setConfig(c);

  // set stack pointer
  // retdec::bin2llvmir::AbiWasm* abiwasm =
  // static_cast<retdec::bin2llvmir::AbiWasm*>(abi); auto sp =
  // module->getGlobalVariable("$__stack_pointer", true); if (sp != nullptr) {
  // 	abiwasm->setStackPointer(sp);
  // }

  // decoder_init add ConfigFunction
  // uint32_t i = 0;
  // for (Function& f: module->functions()) {
  // 	retdec::common::Function* cf = const_cast<retdec::common::Function*>(
  // 	c->insertFunction(&f, retdec::common::Address(i*0x1000),
  // retdec::common::Address(i*0x1000+0x999)));

  // 	i++;
  // }

  // Build up all of the passes that we want to do to the module.
  auto &passRegistry = initializeLlvmPasses();
  legacy::PassManager pm;

  // Without this LLVM does more opts than we would like it to.
  // e.g. printf() call -> puts() call
  //
  // Add an appropriate TargetLibraryInfo pass for the module's triple.
  Triple ModuleTriple(module->getTargetTriple());
  TargetLibraryInfoImpl TLII(ModuleTriple);
  // The -disable-simplify-libcalls flag actually disables all builtin optzns.
  TLII.disableAllFunctions();
  pm.add(new TargetLibraryInfoWrapperPass(TLII));

  for (auto &p : config.parameters.llvmPasses) {
    if (auto *info = passRegistry.getPassInfo(p)) {
      auto *pass = info->createPass();
      addPass(pm, pass, info);

      // if (info->getTypeInfo() ==
      // &retdec::bin2llvmir::ProviderInitialization::ID)
      // {
      // 	auto* p =
      // static_cast<retdec::bin2llvmir::ProviderInitialization*>(pass);
      // 	p->setConfig(&config);
      // }
      if (info->getTypeInfo() == &retdec::llvmir2hll::LlvmIr2Hll::ID) {
        auto *p = static_cast<retdec::llvmir2hll::LlvmIr2Hll *>(pass);
        p->setConfig(&config);
      }
    } else {
      throw std::runtime_error("cannot create pass: " + p);
    }
  }

  // Now that we have all of the passes ready, run them.
  pm.run(*module);

  return EXIT_SUCCESS;
}

} // anonymous namespace

const int EXIT_TIMEOUT = 137;
const int EXIT_BAD_ALLOC = 135;

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.
  EnableDebugBuffering = true;

  // Load the default config parameters.
  //
  retdec::config::Config config;
  auto binpath = retdec::utils::getThisBinaryDirectoryPath();
  fs::path configPath(fs::canonical(binpath));
  configPath.append("decompiler-config.json");
  if (fs::exists(configPath)) {
    config = retdec::config::Config::fromFile(configPath.string());
    config.parameters.fixRelativePaths(
        fs::canonical(configPath).parent_path().string());
  } else {
    std::cerr << "cannot find " << configPath << std::endl;
    return 1;
  }

  // cl::ParseCommandLineOptions(argc, argv,
  // 	"convertor of LLVMIR into the target high-level language\n");

  ProgramOptions po(argc, argv, config, config.parameters);
  try {
    po.load();
  } catch (const std::runtime_error &e) {
    Log::error() << Log::Error << e.what() << std::endl;
    return EXIT_FAILURE;
  }

  // Decompile.
  //
  int ret = 0;
  try {
    std::stringstream buffer;
    if (config.parameters.isTimeout()) {
      std::packaged_task<int(retdec::config::Config &)> task(compileModule);
      auto future = task.get_future();
      std::thread thr(std::move(task), std::ref(config));
      auto timeout = std::chrono::seconds(config.parameters.getTimeout());
      if (future.wait_for(timeout) != std::future_status::timeout) {
        thr.join();
        ret = future.get(); // this will propagate exception
      } else {
        thr.detach(); // we leave the thread still running
        Log::error() << "timeout after: " << config.parameters.getTimeout()
                     << " seconds" << std::endl;
        ret = EXIT_TIMEOUT;
      }
    } else {
      ret = compileModule(config);
    }
  } catch (const std::runtime_error &e) {
    Log::error() << Log::Error << e.what() << std::endl;
    ret = EXIT_FAILURE;
  } catch (const std::bad_alloc &e) {
    Log::error() << "catched std::bad_alloc" << std::endl;
    ret = EXIT_BAD_ALLOC;
  }

  return ret;
}
