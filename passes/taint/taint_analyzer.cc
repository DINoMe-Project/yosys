/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "passes/taint/taint_worker.h"
#include <assert.h>
#include <queue>
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN
using Yosys::backend::taint::TaintAnalyzer;
using Yosys::backend::taint::TaintWorker;
struct TaintAnalyzerBackend : public Pass {
  // taint[bit][i]>0 => bit is tainted by state at i cycles ago
  // taint[bit][i]==0 => bit is not tainted by state at i cycles ago

  TaintAnalyzerBackend() : Pass("taint_analyzer", "analyze taint") {}
  void help() YS_OVERRIDE {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    taint_analyzer [options] [filename]\n");
    log("\n");
  }
  void extra_args(std::ostream *&f, std::string &filename,
                  std::vector<std::string> args, size_t argidx) {
    std::string arg = args[argidx];

    if (arg.substr(0, 1) == "-" && arg != "-")
      cmd_error(args, argidx, "Unknown option or option in arguments.");
    if (f != NULL)
      cmd_error(args, argidx, "Extra filename argument in direct file mode.");
    filename = arg;
    std::ofstream *ff = new std::ofstream;
    ff->open(filename.c_str(), std::ofstream::trunc);
    if (ff->fail()) {
      delete ff;
      log_cmd_error("Can't open output file `%s' for writing: %s\n",
                    filename.c_str(), strerror(errno));
    }
    f = ff;

    if (f == NULL) {
      filename = "<stdout>";
      f = &std::cout;
    }
  }
  void execute(std::vector<std::string> args,
               RTLIL::Design *design) YS_OVERRIDE {
    std::map<IdString, pair<int, int>> observe_vars;
    std::set<RTLIL::SigSpec> observe_signals;
    std::string filename;
    size_t argidx;
    log_header(design, "Executing Taint_Reduce backend.\n");
    for (argidx = 1; argidx < args.size(); argidx++) {
      if (args[argidx] == "-observe" && argidx + 1 < args.size()) {
        string var_name = args[++argidx];
        int offset = std::stoi(args[++argidx]);
        int size = std::stoi(args[++argidx]);
        observe_vars["\\" + var_name] = std::make_pair(offset, size);
        continue;
      }
      break;
    }
    filename = args[argidx];
    std::cerr << filename;
    std::ofstream *ff =
        new std::ofstream(filename, std::ofstream::out | std::ofstream::app);
    std::ostream *f = ff;
    if (f == nullptr) {
      f = &std::cout;
    }
    // f=&std::cout;
    std::cerr<<"before process\n";
    assert(design->modules_.size() == 1);
    Module *module = design->top_module();
    for (auto observe_var : observe_vars) {
      auto varname = observe_var.first;
      int offset = observe_var.second.first;
      int size = observe_var.second.second;
      if (module->wire(varname) == nullptr) {
        log("Error observe var name %s\n", log_id(varname));
        return;
      }
      std::cerr << stringf("observe var name %s at %d size =%d\n",
                           log_id(varname), offset, size);
      auto wire = module->wire(varname);
      assert(offset < wire->width);
      assert(size <= wire->width);
      if (size <= 0)
        size = wire->width;
      if (offset <= 0)
        offset = 0;
      observe_signals.insert(SigSpec(wire, offset, size));
    }
    std::cerr<<"begin process\n";

    TaintAnalyzer taint_analyzer(module);
    *f << "hello\n";
    taint_analyzer.Summarize(f, observe_signals);
    log("filename=%s", filename.c_str());
    f->flush();
    ff->close();
  }
} TaintAnalyzerBackend;

PRIVATE_NAMESPACE_END
