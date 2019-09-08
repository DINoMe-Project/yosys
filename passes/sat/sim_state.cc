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
#include "kernel/calc_sym.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/sigtools.h"
#include "kernel/sym_celltypes.h"
#include "kernel/yosys.h"
#include "passes/sat/sim_state_worker.h"
#include <iostream> // std::cout
#include <sstream>
#include <string> // std::string
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN
using RTLIL::StateSym;
using RTLIL::SymConst;

struct SimPass : public Pass {
  SimPass() : Pass("sim_state", "simulate the circuit") {}
  void help() YS_OVERRIDE {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    sim [options] [top-level]\n");
    log("\n");
    log("This command simulates the circuit using the given top-level "
        "module.\n");
    log("\n");
    log("    -vcd <filename>\n");
    log("        write the simulation results to the given VCD file\n");
    log("\n");
    log("    -clock <portname>\n");
    log("        name of top-level clock input\n");
    log("\n");
    log("    -clockn <portname>\n");
    log("        name of top-level clock input (inverse polarity)\n");
    log("\n");
    log("    -reset <portname>\n");
    log("        name of top-level reset input (active high)\n");
    log("\n");
    log("    -resetn <portname>\n");
    log("        name of top-level inverted reset input (active low)\n");
    log("\n");
    log("    -rstlen <integer>\n");
    log("        number of cycles reset should stay active (default: 1)\n");
    log("\n");
    log("    -zinit\n");
    log("        zero-initialize all uninitialized regs and memories\n");
    log("\n");
    log("    -n <integer>\n");
    log("        number of cycles to simulate (default: 20)\n");
    log("\n");
    log("    -a\n");
    log("        include all nets in VCD output, not just those with public "
        "names\n");
    log("\n");
    log("    -w\n");
    log("        writeback mode: use final simulation state as new init "
        "state\n");
    log("\n");
    log("    -d\n");
    log("        enable debug output\n");
    log("\n");
  }
  void execute(std::vector<std::string> args,
               RTLIL::Design *design) YS_OVERRIDE {
    SimStateWorker worker;
    int numcycles = 20;

    log_header(design, "Executing SIM pass (simulate the circuit).\n");

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      if (args[argidx] == "-vcd" && argidx + 1 < args.size()) {
        worker.vcdfile.open(args[++argidx].c_str());
        continue;
      }
      if (args[argidx] == "-n" && argidx + 1 < args.size()) {
        numcycles = atoi(args[++argidx].c_str());
        continue;
      }
      if (args[argidx] == "-rstlen" && argidx + 1 < args.size()) {
        worker.rstlen = atoi(args[++argidx].c_str());
        continue;
      }
      if (args[argidx] == "-clock" && argidx + 1 < args.size()) {
        worker.clock.insert(RTLIL::escape_id(args[++argidx]));
        continue;
      }
      if (args[argidx] == "-clockn" && argidx + 1 < args.size()) {
        worker.clockn.insert(RTLIL::escape_id(args[++argidx]));
        continue;
      }
      if (args[argidx] == "-reset" && argidx + 1 < args.size()) {
        worker.reset.insert(RTLIL::escape_id(args[++argidx]));
        continue;
      }
      if (args[argidx] == "-resetn" && argidx + 1 < args.size()) {
        worker.resetn.insert(RTLIL::escape_id(args[++argidx]));
        continue;
      }
      if (args[argidx] == "-a") {
        worker.hide_internal = false;
        continue;
      }
      if (args[argidx] == "-d") {
        worker.debug = true;
        continue;
      }
      if (args[argidx] == "-w") {
        worker.writeback = true;
        continue;
      }
      if (args[argidx] == "-zinit") {
        worker.zinit = true;
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    Module *top_mod = nullptr;

    if (design->full_selection()) {
      top_mod = design->top_module();
    } else {
      auto mods = design->selected_whole_modules();
      if (GetSize(mods) != 1)
        log_cmd_error("Only one top module must be selected.\n");
      top_mod = mods.front();
    }

    worker.run(top_mod, numcycles);
  }
} SimPass;

PRIVATE_NAMESPACE_END
