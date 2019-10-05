#ifndef _TAINT_WORKER_HEADER
#define _TAINT_WORKER_HEADER
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include <queue>
#include <string>
namespace Yosys {
namespace backend {
namespace taint {
class TaintWorker;
class TaintAnalyzer {
public:
  TaintAnalyzer(TaintWorker *taint_worker);
  TaintAnalyzer(RTLIL::Module *module);
  void Summarize(std::ostream *&f,
                 const std::set<RTLIL::Wire *> &observable_wires);
  void Summarize(std::ostream *&f,
                 const std::set<RTLIL::SigSpec> &observable_signals);
  std::set<RTLIL::Cell *>
  BackwardCells(const std::set<RTLIL::SigSpec> &observable_signals);
  // update cell to only output used_output;
  // Return a new CELL* newcell so that initial cell = final cell+ newcell if
  // the output only uses partial inputs
  RTLIL::Cell *SplitCellByOutput(IdString output_name, RTLIL::Cell *cell,
                                 const std::set<RTLIL::SigBit> &used_output);

private:
  TaintWorker *taint_worker_;
  RTLIL::Module *module_;
  SigMap sigmap;
};
class TaintWorker {
public:
  TaintWorker(RTLIL::Module *module, const pool<IdString> &secret_vars);
  void ListTaint(std::ostream *&f, int start_cycle = 0, int end_cycle = 3);
  int Run(int cycles);
  void NewCycle() { increased_taint_ = false; };
  bool NeedNewCycle() { return increased_taint_; };
  void SumarizeTaint(std::ostream *&f, int start_cycle, int end_cycle);
  std::set<RTLIL::Wire *> GetTaintedWires() { return tainted_wires_; }
  friend TaintAnalyzer;

private:
  vector<Cell *> SortCell(RTLIL::Module *module);
  void InitTaint(const pool<IdString> &taint_vars);
  void SetTaint(const SigSpec &sig, int val, int cycle = 0);
  void SetTaints(const SigSpec &sig, vector<int> vals, int cycle = 0);
  bool IsTainted(const SigBit &bit) { return taint_.count(bit) > 0; }
  int GetTaint(const SigBit &c_bit, int cycle = 0);
  vector<int> GetTaints(const SigSpec &sig, int cycle = 0);
  void TaintBitOp(Cell *cell, int cycle);
  void TaintSigOp(Cell *cell, int cycle);
  std::vector<RTLIL::Cell *> BackwardCell();
  dict<SigBit, std::map<int, int>> taint_;
  dict<SigBit, std::map<int, int>> control_;
  SigMap sigmap;
  RTLIL::Module *module_;
  bool increased_taint_;
  std::set<RTLIL::Wire *> tainted_wires_;
  std::set<RTLIL::SigBit> tainted_bits_;
  std::set<RTLIL::Wire *> untainted_wires_;
  std::set<RTLIL::SigBit> untainted_bits_;
};
} // namespace taint
} // namespace backend
} // namespace Yosys
#endif
