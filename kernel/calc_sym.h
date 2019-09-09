#include "kernel/rtlil.h"
#include "kernel/yosys.h"
#include "z3++.h"
#include <assert.h>
#include <string>
#ifndef CAL_SYM_H
#define CAL_SYM_H

YOSYS_NAMESPACE_BEGIN
extern z3::context z3_context;
static int name_index = 0;
namespace RTLIL {
class SymConst;
static bool prove(const z3::expr &e) {
  // log("prove\n");
  z3::context &c = e.ctx();
  z3::solver s(c);
  s.add(!e);
  return (s.check() == z3::unsat);
}
static z3::expr bit_const(const char *name) {
  return z3_context.bv_const(name, 1);
}
static z3::expr bit_const() {
  return z3_context.bv_const(stringf("auto#%d", name_index++).c_str(), 1);
}
static z3::expr bit_val(bool val) { return z3_context.bv_val(1, &val); }
static bool is_false(z3::expr val) {
  //  std::cerr << "is_f";
  if (val.is_bv() && val.is_app() && val.is_numeral()) {
    //    std::cerr << "is_ffinish";
    return val.get_numeral_int() == 0;
  }
  //  std::cerr << "is_F finish";
  return false;
}
static bool is_true(z3::expr val) {
  bool ret = false;
  //  std::cerr << "is_true";
  if (val.is_bv() && val.is_app() && val.is_numeral()) {
    //  std::cerr << "is_true finish1 " << val << "\n";
    ret = val.get_numeral_int() == 1;
    //  std::cerr << "is_true finish11";
    return ret;
  }
  //  std::cerr << "is_true finish2";
  return false;
}
class StateSym {
  friend SymConst;

private:
  RTLIL::SigBit bit_;

public:
  enum Type : unsigned char {
    Const = 0,
    And = 1,
    Not = 2,
    Or = 3,
    Xor = 4,
    Sym = 5,
    Lt = 6,
    Gt = 7,
    Eq = 8,
    Mux = 9
  };
  z3::expr val_;
  Type op_;
  vector<StateSym> operands_;
  void SetBit(const RTLIL::SigBit &b) {
    bit_ = b;
    if (op_ == Type::Sym) {
      val_ = bit_const(log_signal(b));
    }
  }
  std::string to_string() const { return val_.simplify().to_string(); }
  const z3::expr &to_expr() const { return val_.simplify(); }

  std::string str() const { return to_string(); }
  StateSym(const State &state, const SigBit &b) : val_(bit_val(0)) {
    op_ = Type::Const;
    switch (state) {
    case RTLIL::State::S0:
    case RTLIL::State::S1:
      op_ = Type::Const;
      val_ = bit_val(state == RTLIL::State::S1);
      break;
    default:
      op_ = Type::Sym;
      val_ = bit_const(log_signal(b));
      break;
    }
  }
  StateSym(const z3::expr &e) : val_(bit_val(0)) {
    assert(e.get_sort().bv_size() == 1);
    val_ = e;
  }
  StateSym(const State &state) : val_(bit_val(0)) {
    SigBit b;
    op_ = Type::Const;
    switch (state) {
    case RTLIL::State::S0:
    case RTLIL::State::S1:
      op_ = Type::Const;
      val_ = bit_val(state == RTLIL::State::S1);
      break;
    default:
      op_ = Type::Sym;
      val_ = bit_const(stringf("auto#%d", name_index++).c_str());
      break;
    }
  }
  StateSym(const StateSym &state) : val_(bit_val(0)) {
    op_ = state.op_;
    val_ = state.val_;
    operands_ = state.operands_;
    bit_ = state.bit_;
  }
  StateSym() : val_(bit_val(0)) {
    op_ = Type::Sym;
    val_ = bit_const(stringf("auto#%d", name_index++).c_str());
  }
  static StateSym CreateStateSymByOp(Type op, const vector<StateSym> &a) {
    /*std::cerr << stringf("add op %d", op);
    for (auto aa : a) {
      std::cerr << stringf(" %s", aa.val_.to_string().c_str());
    }*/
    StateSym state_sym;
    // state_sym.op_ = op;
    state_sym.operands_ = a;
    switch (state_sym.op_) {
    case Type::And:
      assert(a.size() == 2);
      state_sym.val_ = a[0].val_ & a[1].val_;
      break;
    case Type::Or:
      assert(a.size() == 2);
      state_sym.val_ = a[0].val_ | a[1].val_;
      break;
    case Type::Xor:
      assert(a.size() == 2);
      state_sym.val_ = a[0].val_ ^ a[1].val_;
      break;
    case Type::Not:
      assert(a.size() == 1);
      state_sym.val_ = ~a[0].val_;
      break;
    case Type::Lt:
      assert(a.size() == 2);
      state_sym.val_ = a[0].val_ < a[1].val_;
      break;
    case Type::Gt:
      assert(a.size() == 2);
      state_sym.val_ = a[0].val_ > a[1].val_;
      break;
    case Type::Eq:
      assert(a.size() == 2);
      state_sym.val_ = a[0].val_ == a[1].val_;
      break;
    case Type::Mux:
      assert(a.size() == 3);
      state_sym.val_ = z3::ite(a[2].val_ == 1, a[1].val_, a[0].val_);
      break;
    default:
      assert(false);
      state_sym.val_ = bit_val(0);
    }
    state_sym.val_ = state_sym.val_.simplify();

    return state_sym;
  }
  RTLIL::State to_state() const {
    //    std::cerr << "to state start";
    RTLIL::State s =
        is_true(val_) ? State::S1 : (is_false(val_) ? State::S0 : State::Sx);

    //    std::cerr << "to state finish";
    return s;
  }
#define CreateOp(_OP, _TYPE)                                                   \
  static StateSym Create##_OP(const vector<StateSym> &a) {                     \
    return CreateStateSymByOp(_TYPE, a);                                       \
  }
#define CreateOpSingle(_OP, _TYPE)                                             \
  static StateSym Create##_OP(const StateSym &a) {                             \
    return CreateStateSymByOp(_TYPE, {a});                                     \
  }
#define CreateOp2(_OP, _TYPE)                                                  \
  static StateSym Create##_OP(const StateSym &a, const StateSym &b) {          \
    return CreateStateSymByOp(_TYPE, vector<StateSym>({a, b}));                \
  }

  static StateSym CreateMux(const StateSym &a, const StateSym &b,
                            const StateSym &s) {
    // log("create Mux\n");
    return CreateStateSymByOp(Type::Mux, vector<StateSym>({a, b, s}));
  }

  CreateOp(And, Type::And);
  CreateOp(Or, Type::Or);
  CreateOp(Xor, Type::Xor);
  CreateOp(Not, Type::Not);
  CreateOp(Gt, Type::Gt);
  CreateOp(Lt, Type::Lt);
  CreateOp2(Eq, Type::Eq);
  CreateOpSingle(Not, Type::Not);
  bool operator==(const State &other) const {
    //  std::cerr << "==" << val_ << "\n";
    if (val_.is_bv() && val_.is_app()) {
      if (other == State::S0)
        return is_false(val_);
      return is_true(val_);
    } else {
      return false;
    }
  }
  bool operator==(const StateSym &other) const {
    return prove(other.val_ == val_);
  }
  bool operator!=(const StateSym &other) const { return !(other == *this); }
  bool is_const() const { return val_.is_bv() && val_.is_app(); }
}; // namespace RTLIL

struct SymConst {
  int flags;
  z3::expr_vector bits;
  RTLIL::SigSpec signal;
  enum Type : unsigned char { Bit, Add };
  Type type_;
  size_t size() const { return bits.size(); }
  z3::expr_vector reversed_bits() const {
    z3::expr_vector new_bits = bits;
    int size = bits.size();
    for (int i = 0; i < size; ++i) {
      new_bits[i] = bits[size - i];
    }
    return new_bits;
  }
  z3::expr to_expr() const { return z3::concat(reversed_bits()).simplify(); }

  SymConst() : bits(z3_context) {}
  SymConst(std::string str, const RTLIL::SigSpec &sig = RTLIL::SigSpec());
  SymConst(int val, int width = 1,
           const RTLIL::SigSpec &sig = RTLIL::SigSpec());
  SymConst(RTLIL::StateSym bit, int width = 1,
           const RTLIL::SigSpec &sig = RTLIL::SigSpec());
  SymConst(const RTLIL::SigSpec &sig) : type_(Type::Bit), bits(z3_context) {}
  SymConst(RTLIL::Const c, const RTLIL::SigSpec &sig = RTLIL::SigSpec())
      : type_(Type::Bit), bits(z3_context) {
    for (auto b : c.bits)
      bits.push_back(StateSym(b).val_);
    signal = sig;
  };
  SymConst(const RTLIL::SymConst &c) : type_(Type::Bit), bits(z3_context) {
    flags = c.flags;
    bits = c.bits;
    signal = c.signal;
  };
  SymConst(const std::vector<RTLIL::StateSym> &_bits,
           const RTLIL::SigSpec &sig = RTLIL::SigSpec())
      : bits(z3_context), signal(sig) {
    flags = CONST_FLAG_NONE;
    for (auto b : _bits)
      bits.push_back(b.val_.simplify());
  }
  SymConst(const z3::expr_vector &_bits,
           const RTLIL::SigSpec &sig = RTLIL::SigSpec())
      : bits(_bits), signal(sig) {}
  SymConst(const std::vector<bool> &bits,
           const RTLIL::SigSpec &sig = RTLIL::SigSpec());

  SymConst(const z3::expr &ee, int size) : bits(z3_context) {
    z3::expr e = ee.simplify();
    if (e.is_bv()) {
      assert(e.get_sort().bv_size() == size);
      for (int i = 0; i < size; ++i) {
        bits.push_back(e.extract(i, i).simplify());
      }
    } else {
      assert(size == 1);
      bits.push_back(z3::ite(e, bit_val(1), bit_val(0)).simplify());
    }
  }
  SymConst(const z3::expr &e) : bits(z3_context) {
    if (e.is_bv()) {
      int size = e.get_sort().bv_size();
      for (int i = 0; i < size; ++i) {
        bits.push_back(e.extract(i, i));
      }
    } else {
      bits.push_back(z3::ite(e, bit_val(1), bit_val(0)));
    }
  }
  void push_back(const StateSym &s) { bits.push_back(s.val_); }
  RTLIL::Const to_const() {
    RTLIL::Const c;
    for (int i = 0; i < size(); ++i) {
      auto b = bits[i];
      if (is_true(b) || is_false(b))
        c.bits.push_back(is_true(b) ? State::S1 : State::S1);
      else
        c.bits.push_back(RTLIL::Sx);
    }
  }
  bool operator==(const RTLIL::SymConst &other) const;
  bool operator!=(const RTLIL::SymConst &other) const;
  inline const StateSym &operator[](unsigned i) const { return bits[i]; }
  bool as_bool() const;
  int as_int(bool is_signed = false) const;
  std::string as_string() const;
  static SymConst from_string(std::string str);

  std::string decode_string() const;

  bool is_fully_zero() const;
  bool is_fully_ones() const;
  bool is_fully_def() const;
  bool is_fully_undef() const;
  inline RTLIL::SymConst
  extract(int offset, int len = 1,
          RTLIL::StateSym padding = RTLIL::State::S0) const {
    // bits is ordered from big to little
    z3::expr_vector e(z3_context);
    int size = this->size();
    for (int i = 0; i < len; ++i) {
      int pos = size - offset - len + i;
      if (pos < 0) {
        e.push_back(padding.to_expr());
      } else
        e.push_back(bits[pos]);
    }
    return z3::concat(e).simplify();
    // return SymConst(to_expr().extract(offset + len - 1, offset).simplify());
    /*
    ret.bits.reserve(len);
    for (int i = offset; i < offset + len; i++)
      ret.bits.push_back(i < GetSize(bits) ? bits[i] : padding);
    */
  }

  inline unsigned int hash() const {
    unsigned int h = mkhash_init;
    for (int i = 0; i < size(); ++i) {
      auto b = bits[i];
      mkhash(h, b.id());
    }
    return h;
  }
}; // namespace RTLIL

RTLIL::SymConst SymConst_not(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_and(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_or(const RTLIL::SymConst &arg1,
                            const RTLIL::SymConst &arg2, bool signed1,
                            bool signed2, int result_len);
RTLIL::SymConst SymConst_xor(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_xnor(const RTLIL::SymConst &arg1,
                              const RTLIL::SymConst &arg2, bool signed1,
                              bool signed2, int result_len);

RTLIL::SymConst SymConst_reduce_and(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len);
RTLIL::SymConst SymConst_reduce_or(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len);
RTLIL::SymConst SymConst_reduce_xor(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len);
RTLIL::SymConst SymConst_reduce_xnor(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len);
RTLIL::SymConst SymConst_reduce_bool(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len);

RTLIL::SymConst SymConst_logic_not(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len);
RTLIL::SymConst SymConst_logic_and(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len);
RTLIL::SymConst SymConst_logic_or(const RTLIL::SymConst &arg1,
                                  const RTLIL::SymConst &arg2, bool signed1,
                                  bool signed2, int result_len);

RTLIL::SymConst SymConst_shl(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_shr(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_sshl(const RTLIL::SymConst &arg1,
                              const RTLIL::SymConst &arg2, bool signed1,
                              bool signed2, int result_len);
RTLIL::SymConst SymConst_sshr(const RTLIL::SymConst &arg1,
                              const RTLIL::SymConst &arg2, bool signed1,
                              bool signed2, int result_len);
RTLIL::SymConst SymConst_shift(const RTLIL::SymConst &arg1,
                               const RTLIL::SymConst &arg2, bool signed1,
                               bool signed2, int result_len);
RTLIL::SymConst SymConst_shiftx(const RTLIL::SymConst &arg1,
                                const RTLIL::SymConst &arg2, bool signed1,
                                bool signed2, int result_len);

RTLIL::SymConst SymConst_lt(const RTLIL::SymConst &arg1,
                            const RTLIL::SymConst &arg2, bool signed1,
                            bool signed2, int result_len);
RTLIL::SymConst SymConst_le(const RTLIL::SymConst &arg1,
                            const RTLIL::SymConst &arg2, bool signed1,
                            bool signed2, int result_len);
RTLIL::SymConst SymConst_eq(const RTLIL::SymConst &arg1,
                            const RTLIL::SymConst &arg2, bool signed1,
                            bool signed2, int result_len);
RTLIL::SymConst SymConst_ne(const RTLIL::SymConst &arg1,
                            const RTLIL::SymConst &arg2, bool signed1,
                            bool signed2, int result_len);
RTLIL::SymConst SymConst_eqx(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_nex(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_ge(const RTLIL::SymConst &arg1,
                            const RTLIL::SymConst &arg2, bool signed1,
                            bool signed2, int result_len);
RTLIL::SymConst SymConst_gt(const RTLIL::SymConst &arg1,
                            const RTLIL::SymConst &arg2, bool signed1,
                            bool signed2, int result_len);

RTLIL::SymConst SymConst_add(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_sub(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_mul(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_div(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_mod(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_pow(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);

RTLIL::SymConst SymConst_pos(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
RTLIL::SymConst SymConst_neg(const RTLIL::SymConst &arg1,
                             const RTLIL::SymConst &arg2, bool signed1,
                             bool signed2, int result_len);
} // namespace RTLIL
YOSYS_NAMESPACE_END
#endif
