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
#include <iostream> // std::cout
#include <sstream>
#include <string> // std::string
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN
using RTLIL::StateSym;
using RTLIL::SymConst;
struct SimShared {
  bool debug = false;
  bool hide_internal = true;
  bool writeback = false;
  bool zinit = false;
  int rstlen = 1;
};

void zinit(SymConst &v) {
  for (int i = 0; i < v.size(); ++i) {
    if (!RTLIL::is_true(v.bits[i]))
      v.bits[i] = RTLIL::bit_val(0);
  }
}

struct SimInstance {
  SimShared *shared;
  Module *module;
  Cell *instance;
  int cycle_;
  SimInstance *parent;
  dict<Cell *, SimInstance *> children;

  SigMap sigmap;
  dict<SigBit, RTLIL::StateSym> state_nets;
  dict<SigBit, RTLIL::StateSym> init_state_nets;

  dict<SigBit, pool<Cell *>> upd_cells;
  dict<SigBit, pool<Wire *>> upd_outports;

  pool<SigBit> dirty_bits;
  pool<Cell *> dirty_cells;
  pool<SimInstance *, hash_ptr_ops> dirty_children;

  struct ff_state_t {
    StateSym past_clock;
    SymConst past_d;
  };

  struct mem_state_t {
    SymConst past_wr_clk;
    SymConst past_wr_en;
    SymConst past_wr_addr;
    SymConst past_wr_data;
    SymConst data;
  };

  dict<Cell *, ff_state_t> ff_database;
  dict<Cell *, mem_state_t> mem_database;
  pool<Cell *> formal_database;

  dict<Wire *, pair<int, SymConst>> vcd_database;

  SimInstance(SimShared *shared, Module *module, Cell *instance = nullptr,
              SimInstance *parent = nullptr)
      : shared(shared), module(module), instance(instance), parent(parent),
        sigmap(module){
    if (parent) {
      log_assert(parent->children.count(instance) == 0);
      parent->children[instance] = this;
    }
    // std::cerr << "sim instance 1 wire at module
    // "<<module<<"size="<<module->wires().size();
    for (auto wire : module->wires()) {
      //  std::cerr << "sim instance 1.00";
      SigSpec sig = sigmap(wire);
      // std::cerr << "sim instance 1.0";
      for (int i = 0; i < GetSize(sig); i++) {
        if (state_nets.count(sig[i]) == 0) {
          state_nets[sig[i]] = StateSym(State::Sx, sig[i]);
        }
        if (wire->port_output) {
          upd_outports[sig[i]].insert(wire);
          dirty_bits.insert(sig[i]);
        }
      }
      /*if (wire->attributes.count("\\init")) {
        SymConst initval = wire->attributes.at("\\init");
        for (int i = 0; i < GetSize(sig) && i < GetSize(initval); i++)
          if (initval[i] == State::S0 || initval[i] == State::S1) {
            state_nets[sig[i]] = initval[i];
            dirty_bits.insert(sig[i]);
          }
      }*/
      init_state_nets = state_nets;
    }
    for (auto cell : module->cells()) {
      Module *mod = module->design->module(cell->type);

      if (mod != nullptr) {
        dirty_children.insert(new SimInstance(shared, mod, cell, this));
      }

      for (auto &port : cell->connections()) {
        if (cell->input(port.first))
          for (auto bit : sigmap(port.second))
            upd_cells[bit].insert(cell);
      }

      if (cell->type.in("$dff")) {
        ff_state_t ff;
        ff.past_clock = State::Sx;
        ff.past_d = SymConst(State::Sx, cell->getParam("\\WIDTH").as_int());
        ff_database[cell] = ff;
      }

      if (cell->type == "$mem") {
        mem_state_t mem;

        mem.past_wr_clk = SymConst(cell->getPort("\\WR_CLK"));
        mem.past_wr_en = SymConst(cell->getPort("\\WR_EN"));
        mem.past_wr_addr = SymConst(cell->getPort("\\WR_ADDR"));
        mem.past_wr_data = SymConst(cell->getPort("\\WR_DATA"));

        mem.data = SymConst(cell->getParam("\\INIT"));
        int sz = cell->getParam("\\SIZE").as_int() *
                 cell->getParam("\\WIDTH").as_int();

        if (GetSize(mem.data) > sz)
          mem.data.bits.resize(sz);

        while (GetSize(mem.data) < sz)
          mem.data.push_back(StateSym(
              State::Sx, cell->getPort("\\RD_DATA")[GetSize(mem.data)]));

        mem_database[cell] = mem;
      }

      if (cell->type.in("$assert", "$cover", "$assume")) {
        formal_database.insert(cell);
      }
    }
    // std::cerr << "sim instance 3";
    if (shared->zinit) {
      for (auto &it : ff_database) {
        Cell *cell = it.first;
        ff_state_t &ff = it.second;
        zinit(ff.past_d);
        SigSpec qsig = cell->getPort("\\Q");
        SymConst qdata = get_state(qsig);
        zinit(qdata);
        set_state(qsig, qdata);
      }

      for (auto &it : mem_database) {
        mem_state_t &mem = it.second;
        zinit(mem.past_wr_en);
        zinit(mem.data);
      }
    }
    //  std::cerr << "sim instance 4";
  }

  ~SimInstance() {
    for (auto child : children)
      delete child.second;
  }

  IdString name() const {
    if (instance != nullptr)
      return instance->name;
    return module->name;
  }

  std::string hiername() const {
    if (instance != nullptr)
      return parent->hiername() + "." + log_id(instance->name);

    return log_id(module->name);
  }
  SymConst get_init_state(SigSpec sig) {
    SymConst value;
    value.signal = sigmap(sig);
    for (auto bit : value.signal)
      if (bit.wire == nullptr)
        value.push_back(bit.data);
      else if (init_state_nets.count(bit))
        value.push_back(init_state_nets.at(bit));
      else
        value.push_back(State::Sz);

    if (shared->debug)
      log("[%s] get %s: %s\n", hiername().c_str(), log_signal(sig),
          value.as_string().c_str());

    return value;
  }
  SymConst get_state(SigSpec sig) {
    SymConst value;
    value.signal = sigmap(sig);
    for (auto bit : value.signal)
      if (bit.wire == nullptr)
        value.push_back(bit.data);
      else if (state_nets.count(bit))
        value.push_back(state_nets.at(bit));
      else
        value.push_back(State::Sz);

    if (shared->debug)
      log("[%s] get %s: %s\n", hiername().c_str(), log_signal(sig),
          value.as_string().c_str());

    return value;
  }

  bool set_state(SigSpec sig, SymConst value) {
    bool did_something = false;
    value.signal = sig;
    sig = sigmap(sig);
    //	log("sig %s val %s : %d
    //%d\n",log_signal(sig),value.as_string().c_str(),GetSize(sig)
    //,GetSize(value));
    if (GetSize(sig) != GetSize(value)) {
      log_error("sig %s val %s : %d %d", log_signal(sig),
                value.as_string().c_str(), GetSize(sig), GetSize(value));
    }
    log_assert(GetSize(sig) == GetSize(value));
    for (int i = 0; i < GetSize(sig); i++) {
      if (!(state_nets.at(sig[i]) == value[i])) {
        //log("%s, %s \n", state_nets.at(sig[i]).to_string().c_str(),
        //    value[i].to_string().c_str());
        state_nets.at(sig[i]) = value[i];
        dirty_bits.insert(sig[i]);

        did_something = true;
      }
    }
    if (shared->debug)
      log("[%s] set %s: %s\n", hiername().c_str(), log_signal(sig),
          value.as_string().c_str());
    return did_something;
  }

  void update_cell(Cell *cell) {
    //  log_cell(cell);
    log("%s\n", log_id(cell->type));
    if (ff_database.count(cell))
      return;

    if (formal_database.count(cell))
      return;

    if (mem_database.count(cell)) {
      mem_state_t &mem = mem_database.at(cell);

      int num_rd_ports = cell->getParam("\\RD_PORTS").as_int();

      int size = cell->getParam("\\SIZE").as_int();
      int offset = cell->getParam("\\OFFSET").as_int();
      int abits = cell->getParam("\\ABITS").as_int();
      int width = cell->getParam("\\WIDTH").as_int();

      if (cell->getParam("\\RD_CLK_ENABLE").as_bool())
        log_error(
            "Memory %s.%s has clocked read ports. Run 'memory' with -nordff.\n",
            log_id(module), log_id(cell));

      SigSpec rd_addr_sig = cell->getPort("\\RD_ADDR");
      SigSpec rd_data_sig = cell->getPort("\\RD_DATA");

      for (int port_idx = 0; port_idx < num_rd_ports; port_idx++) {
        SymConst addr = get_state(rd_addr_sig.extract(port_idx * abits, abits));
        SymConst data = SymConst(State::Sx, width);

        if (addr.is_fully_def()) {
          int index = addr.as_int() - offset;
          if (index >= 0 && index < size)
            data = mem.data.extract(index * width, width);
        }
        set_state(rd_data_sig.extract(port_idx * width, width), data);
      }
      return;
    }

    if (children.count(cell)) {
      auto child = children.at(cell);
      for (auto &conn : cell->connections())
        if (cell->input(conn.first)) {
          SymConst value = get_state(conn.second);
          child->set_state(child->module->wire(conn.first), value);
        }
      dirty_children.insert(child);
      return;
    }

    if (yosys_celltypes.cell_evaluable(cell->type)) {
      RTLIL::SigSpec sig_a, sig_b, sig_c, sig_d, sig_s, sig_y;
      bool has_a, has_b, has_c, has_d, has_s, has_y;

      has_a = cell->hasPort("\\A");
      has_b = cell->hasPort("\\B");
      has_c = cell->hasPort("\\C");
      has_d = cell->hasPort("\\D");
      has_s = cell->hasPort("\\S");
      has_y = cell->hasPort("\\Y");

      if (has_a)
        sig_a = cell->getPort("\\A");
      if (has_b)
        sig_b = cell->getPort("\\B");
      if (has_c)
        sig_c = cell->getPort("\\C");
      if (has_d)
        sig_d = cell->getPort("\\D");
      if (has_s)
        sig_s = cell->getPort("\\S");
      if (has_y)
        sig_y = cell->getPort("\\Y");

      if (shared->debug)
        log("[%s] eval %s (%s)\n", hiername().c_str(), log_id(cell),
            log_id(cell->type));

      // Simple (A -> Y) and (A,B -> Y) cells
      if (has_a && !has_c && !has_d && !has_s && has_y) {
        set_state(sig_y,
                  SymCellTypes::eval(cell, get_state(sig_a), get_state(sig_b)));
        return;
      }

      // (A,B,C -> Y) cells
      if (has_a && has_b && has_c && !has_d && !has_s && has_y) {
        set_state(sig_y,
                  SymCellTypes::eval(cell, get_state(sig_a), get_state(sig_b),
                                     get_state(sig_c)));
        return;
      }

      // (A,B,S -> Y) cells
      if (has_a && has_b && !has_c && !has_d && has_s && has_y) {
        set_state(sig_y,
                  SymCellTypes::eval(cell, get_state(sig_a), get_state(sig_b),
                                     get_state(sig_s)));
        return;
      }

      log_warning("Unsupported evaluable cell type: %s (%s.%s)\n",
                  log_id(cell->type), log_id(module), log_id(cell));
      return;
    }

    log_error("Unsupported cell type: %s (%s.%s)\n", log_id(cell->type),
              log_id(module), log_id(cell));
  }

  void update_ph1() {
    pool<Cell *> queue_cells;
    pool<Wire *> queue_outports;

    queue_cells.swap(dirty_cells);

    while (1) {
      for (auto bit : dirty_bits) {
        if (upd_cells.count(bit))
          for (auto cell : upd_cells.at(bit))
            queue_cells.insert(cell);

        if (upd_outports.count(bit) && parent != nullptr)
          for (auto wire : upd_outports.at(bit))
            queue_outports.insert(wire);
      }

      dirty_bits.clear();

      if (!queue_cells.empty()) {
        for (auto cell : queue_cells){
          update_cell(cell);
          std::cerr<<"finish update cell\n";
}
        queue_cells.clear();
        continue;
      }

      for (auto wire : queue_outports)
        if (instance->hasPort(wire->name)) {
          // std::cerr<<"updat port";
          SymConst value = get_state(wire);
          parent->set_state(instance->getPort(wire->name), value);
        }

      queue_outports.clear();

      for (auto child : dirty_children)
        child->update_ph1();

      dirty_children.clear();

      if (dirty_bits.empty())
        break;
    }
  }

  bool update_ph2() {
    bool did_something = false;

    for (auto &it : ff_database) {
      Cell *cell = it.first;
      ff_state_t &ff = it.second;

      if (cell->type.in("$dff")) {
        bool clkpol = cell->getParam("\\CLK_POLARITY").as_bool();
        StateSym current_clock = get_state(cell->getPort("\\CLK"))[0];

        if (clkpol ? (ff.past_clock == State::S1 || current_clock != State::S1)
                   : (ff.past_clock == State::S0 || current_clock != State::S0))
          continue;

        if (set_state(cell->getPort("\\Q"), ff.past_d)) {
          log("%s is changed to ", log_signal(cell->getPort("\\Q")));
          log("%s\n",ff.past_d.as_string().c_str());
          did_something = true;
        }
      }
    }

    for (auto &it : mem_database) {
      Cell *cell = it.first;
      mem_state_t &mem = it.second;

      int num_wr_ports = cell->getParam("\\WR_PORTS").as_int();

      int size = cell->getParam("\\SIZE").as_int();
      int offset = cell->getParam("\\OFFSET").as_int();
      int abits = cell->getParam("\\ABITS").as_int();
      int width = cell->getParam("\\WIDTH").as_int();

      SymConst wr_clk_enable = cell->getParam("\\WR_CLK_ENABLE");
      SymConst wr_clk_polarity = cell->getParam("\\WR_CLK_POLARITY");
      SymConst current_wr_clk = get_state(cell->getPort("\\WR_CLK"));

      for (int port_idx = 0; port_idx < num_wr_ports; port_idx++) {
        SymConst addr, data, enable;

        if (wr_clk_enable[port_idx] == State::S0) {
          addr = get_state(
              cell->getPort("\\WR_ADDR").extract(port_idx * abits, abits));
          data = get_state(
              cell->getPort("\\WR_DATA").extract(port_idx * width, width));
          enable = get_state(
              cell->getPort("\\WR_EN").extract(port_idx * width, width));
        } else {
          if (wr_clk_polarity[port_idx] == State::S1
                  ? (mem.past_wr_clk[port_idx] == State::S1 ||
                     current_wr_clk[port_idx] != State::S1)
                  : (mem.past_wr_clk[port_idx] == State::S0 ||
                     current_wr_clk[port_idx] != State::S0))
            continue;

          addr = mem.past_wr_addr.extract(port_idx * abits, abits);
          data = mem.past_wr_data.extract(port_idx * width, width);
          enable = mem.past_wr_en.extract(port_idx * width, width);
        }

        if (addr.is_fully_def()) {
          int index = addr.as_int() - offset;
          if (index >= 0 && index < size)
            for (int i = 0; i < width; i++)
              if (enable[i] == State::S1 &&
                  mem.data[index * width + i] != data[i]) {
                mem.data.bits[index * width + i] = data.bits[i];
                dirty_cells.insert(cell);
                did_something = true;
              }
        }
      }
    }

    for (auto it : children)
      if (it.second->update_ph2()) {
        dirty_children.insert(it.second);
        did_something = true;
      }

    return did_something;
  }

  void update_ph3() {
    for (auto &it : ff_database) {
      Cell *cell = it.first;
      ff_state_t &ff = it.second;

      if (cell->type.in("$dff")) {
        ff.past_clock = get_state(cell->getPort("\\CLK"))[0];
        ff.past_d = get_state(cell->getPort("\\D"));
      }
    }

    for (auto &it : mem_database) {
      Cell *cell = it.first;
      mem_state_t &mem = it.second;

      mem.past_wr_clk = get_state(cell->getPort("\\WR_CLK"));
      mem.past_wr_en = get_state(cell->getPort("\\WR_EN"));
      mem.past_wr_addr = get_state(cell->getPort("\\WR_ADDR"));
      mem.past_wr_data = get_state(cell->getPort("\\WR_DATA"));
    }

    for (auto cell : formal_database) {
      string label = log_id(cell);
      if (cell->attributes.count("\\src"))
        label = cell->attributes.at("\\src").decode_string();

      StateSym a = get_state(cell->getPort("\\A"))[0];
      StateSym en = get_state(cell->getPort("\\EN"))[0];

      if (cell->type == "$cover" && en == State::S1 && a != State::S1)
        log("Cover %s.%s (%s) reached.\n", hiername().c_str(), log_id(cell),
            label.c_str());

      if (cell->type == "$assume" && en == State::S1 && a != State::S1)
        log("Assumption %s.%s (%s) failed.\n", hiername().c_str(), log_id(cell),
            label.c_str());

      if (cell->type == "$assert" && en == State::S1 && a != State::S1)
        log_warning("Assert %s.%s (%s) failed.\n", hiername().c_str(),
                    log_id(cell), label.c_str());
    }
    for (auto it : children)
      it.second->update_ph3();
  }

  void writeback(pool<Module *> &wbmods) {
    if (wbmods.count(module))
      log_error("Instance %s of module %s is not unique: Writeback not "
                "possible. (Fix by running 'uniquify'.)\n",
                hiername().c_str(), log_id(module));

    wbmods.insert(module);

    for (auto wire : module->wires())
      wire->attributes.erase("\\init");

    for (auto &it : ff_database) {
      Cell *cell = it.first;
      SigSpec sig_q = cell->getPort("\\Q");
      SymConst initval = get_state(sig_q);

      for (int i = 0; i < GetSize(sig_q); i++) {
        Wire *w = sig_q[i].wire;

        if (w->attributes.count("\\init") == 0)
          w->attributes["\\init"] = Const(State::Sx, GetSize(w));

        w->attributes["\\init"][sig_q[i].offset] = initval[i].to_state();
      }
    }

    for (auto &it : mem_database) {
      Cell *cell = it.first;
      mem_state_t &mem = it.second;
      SymConst initval = mem.data;

      while (GetSize(initval) >= 2) {
        if (initval[GetSize(initval) - 1] != State::Sx)
          break;
        if (initval[GetSize(initval) - 2] != State::Sx)
          break;
        initval.bits.pop_back();
      }

      cell->setParam("\\INIT", initval.to_const());
    }

    for (auto it : children)
      it.second->writeback(wbmods);
  }

  void write_vcd_header(std::ofstream &f, int &id) {
    // f << stringf("$scope module %s $end\n", log_id(name()));

    for (auto wire : module->wires()) {
      if (shared->hide_internal && wire->name[0] == '$')
        continue;

      // f << stringf("$var wire %d n%d %s%s $end\n", GetSize(wire), id,
      //             wire->name[0] == '$' ? "\\" : "", log_id(wire));
      vcd_database[wire] = make_pair(id++, Const());
    }

    for (auto child : children)
      child.second->write_vcd_header(f, id);

    // f << stringf("$upscope $end\n");
  }

  int write_vcd_step(std::ofstream &f) {
    int outsize = 0;
    for (auto &it : vcd_database) {
      Wire *wire = it.first;
      SymConst value = get_state(wire);
      // std::cerr << "get_state\n";
      int id = it.second.first;
      it.second.second = value;
      std::stringstream s;
      // s << "#b";
      s << value.as_string();
      /*for (int i = GetSize(value) - 1; i >= 0; i--) {
        outsize++;
        s << value[i].to_string();
      }*/
      f << stringf("%d %s %s\n", cycle_, log_id(wire->name), s.str().c_str());
    }

    for (auto child : children)
      outsize += child.second->write_vcd_step(f);

    log("sim size= %d", outsize);
    return outsize;
  }
};

struct SimStateWorker : SimShared {
  SimInstance *top = nullptr;
  bool update_dff=true;
  std::ofstream vcdfile;
  pool<IdString> clock, clockn, reset, resetn;

  ~SimStateWorker() { delete top; }

  void write_vcd_header() {
    if (!vcdfile.is_open())
      return;

    int id = 1;
    top->write_vcd_header(vcdfile, id);

    vcdfile << stringf("$enddefinitions $end\n");
  }

  void write_vcd_step(int t) {
    if (!vcdfile.is_open())
      return;

    vcdfile << stringf("#%d\n", t);
    top->cycle_ = t / 10;
    top->write_vcd_step(vcdfile);
  }

  void update() {
    while (1) {
      std::cerr << "ph1\n";
      if (debug)
        log("\n-- ph1 --\n");
      top->update_ph1();
      if (!update_dff) {
        break;
      }
      std::cerr << "ph2\n";
      if (debug)
        log("\n-- ph2 --\n");

      if (!top->update_ph2())
        break;
    }

    if (debug)
      log("\n-- ph3 --\n");
    top->update_ph3();
  }

  void set_inports(pool<IdString> ports, StateSym value) {
    for (auto portname : ports) {
      Wire *w = top->module->wire(portname);

      if (w == nullptr)
        log_error("Can't find port %s on module %s.\n", log_id(portname),
                  log_id(top->module));
      top->set_state(w, SymConst(value, w->width, w));
    }
  }

  void run(Module *topmod, int numcycles) {
    log_assert(top == nullptr);
    // std::cerr << "new instance";
    top = new SimInstance(this, topmod);

    if (debug)
      log("\n===== 0 =====\n");
    else
      std::cerr << ("Simulating cycle 0.\n");
    set_inports(reset, State::S1);
    set_inports(resetn, State::S0);
    set_inports(clock, State::Sx);
    set_inports(clockn, State::Sx);
    // std::cerr << "update1";
    update();
    // std::cerr << "update2";
    write_vcd_header();
    //    std::cerr << "update3";
    write_vcd_step(0);

    for (int cycle = 0; cycle < numcycles; cycle++) {
      if (debug)
        log("\n===== %d =====\n", 10 * cycle + 5);

      set_inports(clock, State::S0);
      set_inports(clockn, State::S1);
      std::cerr << "update\n";
      update();
      // write_vcd_step(10 * cycle + 5);

      if (debug)
        log("\n===== %d =====\n", 10 * cycle + 10);
      else
        log("Simulating cycle %d.\n", cycle + 1);

      set_inports(clock, State::S1);
      set_inports(clockn, State::S0);

      if (cycle + 1 == rstlen) {
        set_inports(reset, State::S0);
        set_inports(resetn, State::S1);
      }
      update();
      // write_vcd_step(10 * cycle + 10);
    }

    write_vcd_step(10 * numcycles + 2);

    if (writeback) {
      pool<Module *> wbmods;
      top->writeback(wbmods);
    }
  }
};

PRIVATE_NAMESPACE_END
