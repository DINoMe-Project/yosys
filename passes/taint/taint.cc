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
struct TaintBackend : public Pass {
  // taint[bit][i]>0 => bit is tainted by state at i cycles ago
  // taint[bit][i]==0 => bit is not tainted by state at i cycles ago

  TaintBackend() : Pass("taint", "analyze taint") {}
  void help() YS_OVERRIDE {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    taint [options] [filename]\n");
    log("\n");
    log("Write a SMT-LIBv2 [1] description of the current design. For a module "
        "with name\n");
    log("'<mod>' this will declare the sort '<mod>_s' (state of the module) "
        "and will\n");
    log("define and declare functions operating on that state.\n");
    log("\n");
    log("The following SMT2 functions are generated for a module with name "
        "'<mod>'.\n");
    log("Some declarations/definitions are printed with a special comment. A "
        "prover\n");
    log("using the SMT2 files can use those comments to collect all relevant "
        "metadata\n");
    log("about the design.\n");
    log("\n");
    log("    ; yosys-smt2-module <mod>\n");
    log("    (declare-sort |<mod>_s| 0)\n");
    log("        The sort representing a state of module <mod>.\n");
    log("\n");
    log("    (define-fun |<mod>_h| ((state |<mod>_s|)) Bool (...))\n");
    log("        This function must be asserted for each state to establish "
        "the\n");
    log("        design hierarchy.\n");
    log("\n");
    log("    ; yosys-smt2-input <wirename> <width>\n");
    log("    ; yosys-smt2-output <wirename> <width>\n");
    log("    ; yosys-smt2-register <wirename> <width>\n");
    log("    ; yosys-smt2-wire <wirename> <width>\n");
    log("    (define-fun |<mod>_n <wirename>| (|<mod>_s|) (_ BitVec "
        "<width>))\n");
    log("    (define-fun |<mod>_n <wirename>| (|<mod>_s|) Bool)\n");
    log("        For each port, register, and wire with the 'keep' attribute "
        "set an\n");
    log("        accessor function is generated. Single-bit wires are returned "
        "as Bool,\n");
    log("        multi-bit wires as BitVec.\n");
    log("\n");
    log("    ; yosys-smt2-cell <submod> <instancename>\n");
    log("    (declare-fun |<mod>_h <instancename>| (|<mod>_s|) "
        "|<submod>_s|)\n");
    log("        There is a function like that for each hierarchical instance. "
        "It\n");
    log("        returns the sort that represents the state of the sub-module "
        "that\n");
    log("        implements the instance.\n");
    log("\n");
    log("    (declare-fun |<mod>_is| (|<mod>_s|) Bool)\n");
    log("        This function must be asserted 'true' for initial states, and "
        "'false'\n");
    log("        otherwise.\n");
    log("\n");
    log("    (define-fun |<mod>_i| ((state |<mod>_s|)) Bool (...))\n");
    log("        This function must be asserted 'true' for initial states. "
        "For\n");
    log("        non-initial states it must be left unconstrained.\n");
    log("\n");
    log("    (define-fun |<mod>_t| ((state |<mod>_s|) (next_state |<mod>_s|)) "
        "Bool (...))\n");
    log("        This function evaluates to 'true' if the states 'state' "
        "and\n");
    log("        'next_state' form a valid state transition.\n");
    log("\n");
    log("    (define-fun |<mod>_a| ((state |<mod>_s|)) Bool (...))\n");
    log("        This function evaluates to 'true' if all assertions hold in "
        "the state.\n");
    log("\n");
    log("    (define-fun |<mod>_u| ((state |<mod>_s|)) Bool (...))\n");
    log("        This function evaluates to 'true' if all assumptions hold in "
        "the state.\n");
    log("\n");
    log("    ; yosys-smt2-assert <id> <filename:linenum>\n");
    log("    (define-fun |<mod>_a <id>| ((state |<mod>_s|)) Bool (...))\n");
    log("        Each $assert cell is converted into one of this functions. "
        "The function\n");
    log("        evaluates to 'true' if the assert statement holds in the "
        "state.\n");
    log("\n");
    log("    ; yosys-smt2-assume <id> <filename:linenum>\n");
    log("    (define-fun |<mod>_u <id>| ((state |<mod>_s|)) Bool (...))\n");
    log("        Each $assume cell is converted into one of this functions. "
        "The function\n");
    log("        evaluates to 'true' if the assume statement holds in the "
        "state.\n");
    log("\n");
    log("    ; yosys-smt2-cover <id> <filename:linenum>\n");
    log("    (define-fun |<mod>_c <id>| ((state |<mod>_s|)) Bool (...))\n");
    log("        Each $cover cell is converted into one of this functions. The "
        "function\n");
    log("        evaluates to 'true' if the cover statement is activated in "
        "the state.\n");
    log("\n");
    log("Options:\n");
    log("\n");
    log("    -verbose\n");
    log("        this will print the recursive walk used to export the "
        "modules.\n");
    log("\n");
    log("    -stbv\n");
    log("        Use a BitVec sort to represent a state instead of an "
        "uninterpreted\n");
    log("        sort. As a side-effect this will prevent use of arrays to "
        "model\n");
    log("        memories.\n");
    log("\n");
    log("    -stdt\n");
    log("        Use SMT-LIB 2.6 style datatypes to represent a state instead "
        "of an\n");
    log("        uninterpreted sort.\n");
    log("\n");
    log("    -nobv\n");
    log("        disable support for BitVec (FixedSizeBitVectors theory). "
        "without this\n");
    log("        option multi-bit wires are represented using the BitVec sort "
        "and\n");
    log("        support for coarse grain cells (incl. arithmetic) is "
        "enabled.\n");
    log("\n");
    log("    -nomem\n");
    log("        disable support for memories (via ArraysEx theory). this "
        "option is\n");
    log("        implied by -nobv. only $mem cells without merged registers "
        "in\n");
    log("        read ports are supported. call \"memory\" with -nordff to "
        "make sure\n");
    log("        that no registers are merged into $mem read ports. '<mod>_m' "
        "functions\n");
    log("        will be generated for accessing the arrays that are used to "
        "represent\n");
    log("        memories.\n");
    log("\n");
    log("    -wires\n");
    log("        create '<mod>_n' functions for all public wires. by default "
        "only ports,\n");
    log("        registers, and wires with the 'keep' attribute are "
        "exported.\n");
    log("\n");
    log("    -tpl <template_file>\n");
    log("        use the given template file. the line containing only the "
        "token '%%%%'\n");
    log("        is replaced with the regular output of this command.\n");
    log("\n");
    log("[1] For more information on SMT-LIBv2 visit http://smt-lib.org/ or "
        "read David\n");
    log("R. Cok's tutorial: "
        "http://www.grammatech.com/resources/smt/SMTLIBTutorial.pdf\n");
    log("\n");
    log("----------------------------------------------------------------------"
        "-----\n");
    log("\n");
    log("Example:\n");
    log("\n");
    log("Consider the following module (test.v). We want to prove that the "
        "output can\n");
    log("never transition from a non-zero value to a zero value.\n");
    log("\n");
    log("        module test(input clk, output reg [3:0] y);\n");
    log("          always @(posedge clk)\n");
    log("            y <= (y << 1) | ^y;\n");
    log("        endmodule\n");
    log("\n");
    log("For this proof we create the following template (test.tpl).\n");
    log("\n");
    log("        ; we need QF_UFBV for this poof\n");
    log("        (set-logic QF_UFBV)\n");
    log("\n");
    log("        ; insert the auto-generated code here\n");
    log("        %%%%\n");
    log("\n");
    log("        ; declare two state variables s1 and s2\n");
    log("        (declare-fun s1 () test_s)\n");
    log("        (declare-fun s2 () test_s)\n");
    log("\n");
    log("        ; state s2 is the successor of state s1\n");
    log("        (assert (test_t s1 s2))\n");
    log("\n");
    log("        ; we are looking for a model with y non-zero in s1\n");
    log("        (assert (distinct (|test_n y| s1) #b0000))\n");
    log("\n");
    log("        ; we are looking for a model with y zero in s2\n");
    log("        (assert (= (|test_n y| s2) #b0000))\n");
    log("\n");
    log("        ; is there such a model?\n");
    log("        (check-sat)\n");
    log("\n");
    log("The following yosys script will create a 'test.smt2' file for our "
        "proof:\n");
    log("\n");
    log("        read_verilog test.v\n");
    log("        hierarchy -check; proc; opt; check -assert\n");
    log("        write_smt2 -bv -tpl test.tpl test.smt2\n");
    log("\n");
    log("Running 'cvc4 test.smt2' will print 'unsat' because y can never "
        "transition\n");
    log("from non-zero to zero in the test design.\n");
    log("\n");
  }
  void extra_args(std::ostream *&f, std::string &filename,
                  std::vector<std::string> args, size_t argidx) {
    bool called_with_fp = f != NULL;

    for (; argidx < args.size(); argidx++) {
      std::string arg = args[argidx];

      if (arg.substr(0, 1) == "-" && arg != "-")
        cmd_error(args, argidx, "Unknown option or option in arguments.");
      if (f != NULL)
        cmd_error(args, argidx, "Extra filename argument in direct file mode.");

      if (arg == "-") {
        filename = "<stdout>";
        f = &std::cout;
        continue;
      }

      filename = arg;
      std::ofstream *ff = new std::ofstream;
      ff->open(filename.c_str(), std::ofstream::trunc);
      yosys_output_files.insert(filename);
      if (ff->fail()) {
        delete ff;
        log_cmd_error("Can't open output file `%s' for writing: %s\n",
                      filename.c_str(), strerror(errno));
      }
      f = ff;
    }

    if (called_with_fp)
      args.push_back(filename);
    args[0] = pass_name;
    // cmd_log_args(args);

    if (f == NULL) {
      filename = "<stdout>";
      f = &std::cout;
    }
  }
  void execute(std::vector<std::string> args,
               RTLIL::Design *design) YS_OVERRIDE {
    pool<IdString> taint_vars;
    std::string filename;
    std::ostream *f = nullptr;
    int cycles = 2;
    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      if (args[argidx] == "-taint" && argidx + 1 < args.size()) {
        string var_name = args[++argidx];
        taint_vars.insert("\\" + var_name);
        continue;
      }
      if (args[argidx] == "-cycles" && argidx + 1 < args.size()) {
        cycles = std::stoi(args[++argidx]);
        continue;
      }
      break;
    }
    extra_args(f, filename, args, argidx);
    assert(design->modules_.size() == 1);
    Module *module = design->top_module();
    for (auto taint_var : taint_vars)
      if (module->wire(taint_var) == nullptr) {
        log("Error taint var name %s\n", log_id(taint_var));
        return;
      }
    TaintWorker taint_worker(module, taint_vars);
    cycles = taint_worker.Run(cycles);
    taint_worker.SumarizeTaint(f, 0, cycles);
    TaintAnalyzer ta(module);
    ta.Summarize(f, taint_worker.GetTaintedWires());
    log("filename=%s", filename.c_str());
  }
} TaintBackend;

PRIVATE_NAMESPACE_END
