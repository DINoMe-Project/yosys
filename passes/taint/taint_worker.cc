#include "passes/taint/taint_worker.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include <assert.h>
#include <queue>
#include <string>
namespace Yosys {
namespace backend {
namespace taint {
namespace {
static bool IsClockCell(Cell *cell) {
  return cell->type.in("$dff", "$_DFF_P_", "$_DFF_N_", "$sr", "$ff", "$dffe",
                       "$dffsr", "$adff", "$dlatchsr") ||
         cell->hasPort("\\CLK") || cell->hasPort("\\C");
}
static bool IsBitOp(Cell *cell) {
  return cell->type.in("$and", "$or", "$xor", "$xnor", "$logic_and",
                       "$logic_or", "$not", "$neg", "$mux") ||
         IsClockCell(cell);
}
} // namespace
vector<Cell *> TaintWorker::SortCell(RTLIL::Module *module) {
  vector<Cell *> sorted_cells;
  std::map<RTLIL::Cell *, std::set<RTLIL::Cell *>> cell_deps;
  std::map<RTLIL::SigBit, RTLIL::Cell *> port_cells;
  for (auto cell : module->cells())
    if (!IsClockCell(cell))
      for (auto conn : cell->connections())
        if (cell->output(conn.first))
          for (auto bit : conn.second) {
            sigmap.apply(bit);
            assert(port_cells.count(bit) == 0);
            port_cells[bit] = cell;
          }

  std::queue<RTLIL::Cell *> cell_queue;
  for (auto cell : module->cells()) {
    for (auto conn : cell->connections())
      if (cell->input(conn.first))
        for (auto bit : conn.second) {
          sigmap.apply(bit);
          if (port_cells.count(bit) > 0)
            cell_deps[cell].insert(port_cells[bit]);
        }

    if (cell_deps.count(cell) == 0) {
      cell_queue.push(cell);
    }
  }
  while (cell_queue.size() > 0) {
    auto cell = cell_queue.front();
    cell_deps.erase(cell);
    cell_queue.pop();
    sorted_cells.push_back(cell);
    vector<RTLIL::Cell *> remove_cells;
    for (auto &dep : cell_deps) {
      dep.second.erase(cell);
      if (dep.second.size() == 0) {
        cell_queue.push(dep.first);
        remove_cells.push_back(dep.first);
      }
    }
    for (auto c : remove_cells) {
      cell_deps.erase(c);
    }
  }
  return sorted_cells;
}
TaintWorker::TaintWorker(RTLIL::Module *module,
                         const pool<IdString> &secret_vars)
    : module_(module), increased_taint_(false) {
  InitTaint(secret_vars);
}

void TaintWorker::SetTaint(const SigSpec &sig, int val, int cycle) {
  for (auto bit : sig) {
    // log("set taint %s at %d: %d\n", log_signal(bit), cycle, val);
    if (val > 0 && taint_[bit].size() == 0) {
      taint_[sigmap(bit)][cycle] = val;
      increased_taint_ = true;
    }
  }
}

void TaintWorker::SetTaints(const SigSpec &sig, vector<int> vals, int cycle) {
  int i = 0;
  for (auto bit : sig) {
    // log("set taint %s at %d: %d\n", log_signal(bit), cycle, vals[i]);
    if (vals[i] > 0 && taint_[bit].size() == 0) {
      taint_[sigmap(bit)][cycle] = vals[i];
      increased_taint_ = true;
    }
    ++i;
  }
}
int TaintWorker::GetTaint(const SigBit &c_bit, int cycle) {
  SigBit bit = c_bit;
  sigmap.apply(bit);
  if (taint_.count(bit) > 0 && taint_[bit].count(cycle) > 0) {
    return taint_[sigmap(bit)][cycle];
  }
  return 0;
}
vector<int> TaintWorker::GetTaints(const SigSpec &sig, int cycle) {
  vector<int> taints;
  for (auto bit : sig) {
    taints.push_back(GetTaint(bit, cycle));
    // log("%s: %d\t",log_signal(bit),taint_[bit]);
  }
  // log("\n");
  return taints;
}
void TaintWorker::InitTaint(const pool<IdString> &taint_vars) {
  // merge signals ini sigmap
  for (auto conn : module_->connections()) {
    // log("connection %s %s\n", log_signal(conn.first),
    // log_signal(conn.second));
    sigmap.add(conn.second, conn.first);
  }
  // log("####module= %s\n", log_id(module_->name));
  for (auto wire : module_->wires()) {
    // log("wire %s %d %d\n", log_id(wire->name), wire->port_input,
    // wire->port_output);
    if (wire->name.in(taint_vars)) {
      SetTaint(wire, 1, 0);
      log("set initial taint %s", log_signal(RTLIL::SigSpec(wire)));
    }
  }
}
void TaintWorker::TaintSigOp(Cell *cell, int cycle) {
  // log_cell(cell);
  pool<IdString> data_signals({"\\A", "\\B", "\\C", "\\D"});
  pool<IdString> out_signals({"\\Y", "\\Q"});
  int taint_cycle = cycle;
  int taint = 0;
  vector<SigSpec> outputs;
  for (auto conn : cell->connections()) {
    if (conn.first.in(data_signals)) {
      auto taints = GetTaints(conn.second, cycle);
      taint = max(taint, *max_element(taints.begin(), taints.end()));
    } else if (conn.first.in(out_signals)) {
      outputs.push_back(conn.second);
    }
  }
  if (IsClockCell(cell)) {
    taint_cycle++;
  }
  for (auto output : outputs) {
    SetTaint(output, taint, taint_cycle);
  }
}
void TaintWorker::TaintBitOp(Cell *cell, int cycle) {
  // log_cell(cell);
  pool<IdString> data_signals({"\\A", "\\B", "\\C", "\\D"});
  pool<IdString> out_signals({"\\Y", "\\Q"});
  pool<IdString> condition_signals({"\\S", "\\E"});
  int taint_cycle = cycle;
  vector<SigSpec> outputs;
  if (IsBitOp(cell)) {
    auto output =
        cell->hasPort("\\Y") ? cell->getPort("\\Y") : cell->getPort("\\Q");
    int size = output.size();
    int implicit_taint = 0;
    // port "\\S" is the branch condition.
    for (auto condiction_port : condition_signals) {
      if (cell->hasPort(condiction_port)) {
        auto taints = GetTaints(cell->getPort(condiction_port), cycle);
        assert(taints.size() == 1);
        implicit_taint = max(implicit_taint, taints[0]);
      }
    }
    std::vector<int> final_taints(size, implicit_taint);
    for (auto conn : cell->connections()) {
      if (conn.first.in(data_signals) && !conn.second.is_fully_const()) {
        auto taints = GetTaints(conn.second, cycle);
        for (int i = 0; i < min(int(taints.size()), size); ++i) {
          final_taints[i] = max(final_taints[i], taints[i]);
        }
      }
    }
    if (IsClockCell(cell)) {
      taint_cycle++;
    }
    SetTaints(output, final_taints, taint_cycle);
  }
}
int TaintWorker::Run(int cycles) {
  auto cells = SortCell(module_);
  int cycle = 0;
  for (; cycle < cycles; ++cycle) {
    if (!NeedNewCycle())
      break;
    NewCycle();
    for (auto cell : cells) {
      if (IsBitOp(cell)) {
        TaintBitOp(cell, cycle);
      } else {
        TaintSigOp(cell, cycle);
      }
    }
  }
  log("taint size %d used cycles=%d", int(taint_.size()), cycle);
  return cycle;
}
void TaintWorker::SumarizeTaint(std::ostream *&f, int start_cycle,
                                int end_cycle) {
  for (auto wire : module_->selected_wires()) {
    SigSpec sig(wire);
    auto name = log_signal(wire);
    if (name[0] == '$')
      continue;
    if (wire->port_input)
      continue;
    sigmap.apply(sig);
    bool istainted = false;
    for (auto bit : sig) {
      if (!IsTainted(bit)) {
        untainted_bits_.insert(bit);
        continue;
      }
      istainted = true;
      tainted_bits_.insert(bit);
      tainted_wires_.insert(bit.wire);
    }
    if (!istainted)
      untainted_wires_.insert(wire);
  }
  *f << "Summary: #tainted wires = " << tainted_wires_.size() << "\n";
  *f << "Summary: #tainted bits = " << tainted_bits_.size() << "\n";
  *f << "Summary: #untainted wires = " << untainted_wires_.size() << "\n";
  *f << "Summary: #untainted bits = " << untainted_bits_.size() << "\n";
  for (auto wire : tainted_wires_) {
    auto name = log_signal(wire);
    if (name[0] == '$')
      continue;
    *f << name << ": " << wire->width << "\n";
  }
  for (auto bit : tainted_bits_) {
    auto name = log_signal(bit);
    if (name[0] == '$')
      continue;
    *f << name << ":";
    for (int cycle = start_cycle; cycle <= end_cycle; ++cycle)
      *f << GetTaint(bit, cycle) << " ";
    *f << "\n";
  }
}
TaintAnalyzer::TaintAnalyzer(RTLIL::Module *module)
    : module_(module), sigmap(module_) {}
void TaintAnalyzer::Summarize(
    std::ostream *&f, const std::set<RTLIL::SigSpec> &observable_signals) {
  // std::vector<RTLIL::Cell*> used_cells;
  std::set<RTLIL::Cell *> used_cell_set;
  std::set<RTLIL::Cell *> unused_cell_set;
  std::set<RTLIL::SigSpec> used_wire_set;
  auto used_cells = BackwardCells(observable_signals);
  *f << "Summary: used cells = " << used_cells.size() << " out of "
     << module_->cells().size() << "\n";
  for (auto cell : used_cells) {
    used_cell_set.insert(cell);
    for (auto conn : cell->connections())
      for (auto b : conn.second)
        if (b.wire) {
          // log("used wire %s as
          // %s\n",log_id(b.wire->name),log_signal(sigmap(b.wire)));
          used_wire_set.insert(sigmap(b.wire));
        }
  }
  *f << "Summary: used wires = " << used_wire_set.size() << " out of "
     << module_->wires().size() << "\n";
  for (auto cell : module_->cells()) {
    if (used_cell_set.count(cell) == 0) {
      *f << "unused cell detected:" << log_id(cell->name) << "\n";
      // log("unused cell detected:", log_id(cell->name));
      // log_cell(cell);
      unused_cell_set.insert(cell);
    }
  }
  for (auto cell : unused_cell_set)
    module_->remove(cell);
  if (module_->cells().size() != used_cells.size()) {
    *f << "updated module size=" << module_->cells().size() << "\n";
  }
  //->check();
  /*  pool<Wire*> unused_wires;
    for(auto wire : module_->wires()){
      if(used_wire_set.count(sigmap(wire))==0){
        unused_wires.insert(wire);
        log("unused wire %s as
    %s\n",log_id(wire->name),log_signal(sigmap(wire)));
      }
    }
    module_->remove(unused_wires);
    module_->fixup_ports();*/
}

void TaintAnalyzer::Summarize(std::ostream *&f,
                              const std::set<RTLIL::Wire *> &observable_wires) {
  std::set<RTLIL::SigSpec> observable_signals;
  for (auto wire : observable_wires) {
    observable_signals.insert(wire);
  }
  Summarize(f, observable_signals);
}
RTLIL::SigSpec ComposeSigSpecByIndexes(const RTLIL::SigSpec &sig,
                                       const vector<int> &used_index) {
  RTLIL::SigSpec newsig;
  for (auto i : used_index) {
    if (i >= sig.size()) {
      newsig.append(State::S0);
    } else
      newsig.append(sig[i]);
  }
  return newsig;
}
RTLIL::Cell *
TaintAnalyzer::SplitCellByOutput(IdString output_name, RTLIL::Cell *cell,
                                 const std::set<RTLIL::SigBit> &used_output) {
  log("split------:%s\n", log_id(output_name));
  auto outputs = cell->getPort(output_name);
  log("split2\n");
  vector<int> used_index, unused_index;
  std::string used_index_str = " ";
  std::string unused_index_str = " ";
  for (int i = 0; i < outputs.size(); ++i) {
    if (used_output.count(outputs[i]) > 0) {
      used_index.push_back(i);
      used_index_str += std::to_string(i) + ",";
    } else {
      unused_index.push_back(i);
      unused_index_str += std::to_string(i) + ",";
    }
  }
  if (unused_index.size() == 0)
    return nullptr;
  std::string used_cell_name = cell->name.str() + used_index_str,
              unused_cell_name = cell->name.str() + unused_index_str;
  RTLIL::Cell *newcell = module_->addCell(unused_cell_name, cell);
  auto conns = cell->connections();
  for (auto conn : conns) {
    log("new signal %s", log_id(conn.first));
    if (conn.first.in("\\A", "\\B", "\\D", "\\Y", "\\C", "\\Q")) {
      log("= %s\n",
          log_signal(ComposeSigSpecByIndexes(conn.second, unused_index)));
      auto new_sig = ComposeSigSpecByIndexes(conn.second, unused_index);
      newcell->setPort(conn.first, new_sig);
      auto update_sig = ComposeSigSpecByIndexes(conn.second, used_index);
      cell->setPort(conn.first, update_sig);
      if (conn.first.in("\\A", "\\B", "\\Y")) {
        std::string port_name = conn.first.str() + "_WIDTH";
        log("param %s = %d %d\n", port_name.c_str(), new_sig.size(),
            update_sig.size());
        if (cell->hasParam(port_name)) {
          newcell->setParam(port_name, new_sig.size());
          cell->setParam(port_name, update_sig.size());
        }
      }
    }
  }
  if (cell->hasParam("\\WIDTH")) {
    log("width=%d", used_index.size());
    newcell->setParam("\\WIDTH", unused_index.size());
    cell->setParam("\\WIDTH", used_index.size());
  }
  module_->rename(cell, used_cell_name);
  return newcell;
}
std::set<RTLIL::Cell *> TaintAnalyzer::BackwardCells(
    const std::set<RTLIL::SigSpec> &observable_signals) {
  std::map<RTLIL::SigBit, RTLIL::Cell *> port_cells;
  std::set<RTLIL::Cell *> backward_cells;
  std::queue<RTLIL::Cell *> cell_queue;
  std::map<Cell *, std::pair<RTLIL::IdString, RTLIL::SigSpec>> cell_sig;
  std::set<RTLIL::SigBit> used_bits;
  std::cerr << "before process 2\n";

  IdString output_name = "\\Y";
  for (auto cell : module_->cells())
    for (auto conn : cell->connections())
      if (cell->output(conn.first)) {
        for (auto bit : conn.second) {
          sigmap.apply(bit);
          assert(port_cells.count(bit) == 0);
          port_cells[bit] = cell;
          cell_sig[cell] = conn;
        }
      }
  for (auto sig : observable_signals) {
    sigmap.apply(sig);
    auto bitset = sig.to_sigbit_set();
    used_bits.insert(sig.begin(), sig.end());
    for (auto bit : sig)
      if (port_cells.count(bit) > 0)
        if (cell_sig.count(port_cells[bit]) > 0) {
          RTLIL::Cell *cell = port_cells[bit];
          cell_queue.push(cell);
          for (auto b : cell_sig[cell].second) {
            log("erase cell %s for %s\n", log_id(port_cells[b]), log_signal(b));
            port_cells.erase(b);
          }
        }
  }
  while (!cell_queue.empty()) {
    auto cell = cell_queue.front();
    // log("pop cell %lx\n", cell);
    // log_cell(cell);
    cell_queue.pop();
    //  log("old cell:");
    //  log_cell(cell);
    RTLIL::Cell *newcell = nullptr;
    auto output_name = cell_sig[cell].first;
    cell_sig.erase(cell);
  /*  if (IsClockCell(cell)) {
      newcell = SplitCellByOutput(output_name, cell, used_bits);
    } else if (IsBitOp(cell)) {
      newcell = SplitCellByOutput(output_name, cell, used_bits);
    } else {
      // log("sig cell\n");
      // log_cell(cell);
    }*/
    if (newcell != nullptr) {
      cell_sig[newcell] =
          std::make_pair(output_name, sigmap(newcell->getPort(output_name)));
      log("new cell:");
      log_cell(newcell);
      log("old cell is changed to\n");
      log_cell(cell);
    } else {
      log("empty new cell\n");
    }
    for (auto conn : cell->connections()) {
      used_bits.insert(conn.second.begin(), conn.second.end());
    }
    //  log("add cell");
    //  log_cell(cell);
    backward_cells.insert(cell);

    std::set<RTLIL::Cell *> cells_to_add;
    for (auto conn : cell->connections()) {
      if (cell->input(conn.first))
        for (auto bit : conn.second)
          if (port_cells.count(bit) > 0)
            if (cell_sig.count(port_cells[bit]) > 0) {
              auto c = port_cells[bit];
              cell_queue.push(c);
            //  backward_cells.insert(c);
              for (auto b : cell_sig[c].second)
                port_cells.erase(b);
            }
    }
  }
  return backward_cells;
}
} // namespace taint
} // namespace backend
} // namespace Yosys
