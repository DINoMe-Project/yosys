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

// [[CITE]] Power-Modulus Algorithm
// Schneier, Bruce (1996). Applied Cryptography: Protocols, Algorithms, and
// Source Code in C, Second Edition (2nd ed.). Wiley. ISBN 978-0-471-11709-4,
// page 244

#include "kernel/calc_sym.h"
#include "kernel/yosys.h"
#include "libs/bigint/BigIntegerLibrary.hh"
#include "z3.h"
#include <string>
YOSYS_NAMESPACE_BEGIN
z3::context z3_context;
static z3::expr extend_u0(const z3::expr &e, unsigned width, bool is_signed) {
  unsigned old_width = e.is_bv() ? e.get_sort().bv_size() : 1;
  if (width < old_width) {
//    std::cerr << width << "," << old_width << e << "\n";
    return e.extract(width - 1, 0).simplify();
  }
  if (width - old_width == 0)
    return e;
  z3::expr ee = e;
  if (!e.is_bv()) {
    assert(e.is_bool());
    ee = z3::ite(e, RTLIL::bit_val(1), RTLIL::bit_val(0));
  }
//  std::cerr << "extend" << ee << "is_signed=" << is_signed
  //          << ", width - old_width" << width - old_width;
  z3::expr ret = is_signed ? z3::sext(ee, width - old_width).simplify()
                           : z3::zext(ee, width - old_width).simplify();
  //std::cerr << "return " << ret;
  return ret;
}

RTLIL::SymConst RTLIL::SymConst_not(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &, bool signed1, bool,
                                    int result_len) {
  auto a = extend_u0(arg1.to_expr(), result_len, false);
  return ~a;
}

RTLIL::SymConst RTLIL::SymConst_and(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  auto a = extend_u0(arg1.to_expr(), result_len, false);
  auto b = extend_u0(arg2.to_expr(), result_len, false);
  return RTLIL::SymConst(a & b);
  // return logic_wrapper(logic_and, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::SymConst RTLIL::SymConst_or(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  auto a = extend_u0(arg1.to_expr(), result_len, false);
  auto b = extend_u0(arg2.to_expr(), result_len, false);
  return RTLIL::SymConst(a | b);
  // return logic_wrapper(logic_or, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::SymConst RTLIL::SymConst_xor(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  auto a = extend_u0(arg1.to_expr(), result_len, false);
  auto b = extend_u0(arg2.to_expr(), result_len, false);
  return RTLIL::SymConst(a ^ b);
  // return logic_wrapper(logic_xor, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::SymConst RTLIL::SymConst_xnor(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len) {
  auto a = extend_u0(arg1.to_expr(), result_len, false);
  auto b = extend_u0(arg2.to_expr(), result_len, false);
  return RTLIL::SymConst(z3::xnor(a, b));
  // return logic_wrapper(logic_xnor, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::SymConst RTLIL::SymConst_reduce_and(const RTLIL::SymConst &arg1,
                                           const RTLIL::SymConst &, bool, bool,
                                           int result_len) {
  return RTLIL::SymConst(z3::mk_and(arg1.bits));
  //  return logic_reduce_wrapper(RTLIL::State::S1, logic_and, arg1,
  //  result_len);
}

RTLIL::SymConst RTLIL::SymConst_reduce_or(const RTLIL::SymConst &arg1,
                                          const RTLIL::SymConst &, bool, bool,
                                          int result_len) {
  return RTLIL::SymConst(z3::mk_or(arg1.bits));
}

RTLIL::SymConst RTLIL::SymConst_reduce_xor(const RTLIL::SymConst &arg1,
                                           const RTLIL::SymConst &, bool, bool,
                                           int result_len) {

  size_t size = arg1.size();
  assert(size > 0);
  z3::expr e = arg1[0].to_expr();
  for (size_t i = 1; i < size; ++i) {
    e = (e ^ arg1[i].to_expr()).simplify();
  }
  return RTLIL::SymConst(e, 1);
}

RTLIL::SymConst RTLIL::SymConst_reduce_xnor(const RTLIL::SymConst &arg1,
                                            const RTLIL::SymConst &, bool, bool,
                                            int result_len) {
  size_t size = arg1.size();
  assert(size > 0);
  z3::expr e = arg1[0].to_expr();
  for (size_t i = 1; i < size; ++i) {
    e = z3::xnor(e, arg1[i].to_expr()).simplify();
  }
  return RTLIL::SymConst(e, 1);
}

RTLIL::SymConst RTLIL::SymConst_reduce_bool(const RTLIL::SymConst &arg1,
                                            const RTLIL::SymConst &, bool, bool,
                                            int result_len) {
  size_t size = arg1.size();
  assert(size > 0);
  z3::expr e = arg1.bits[0];
  for (size_t i = 1; i < size; ++i) {
    e = (e | arg1[i].to_expr()).simplify();
  }
  return RTLIL::SymConst(e, 1);
}

RTLIL::SymConst RTLIL::SymConst_logic_not(const RTLIL::SymConst &arg1,
                                          const RTLIL::SymConst &unused,
                                          bool signed1, bool unused2,
                                          int result_len) {
  RTLIL::SymConst result =
      SymConst_reduce_bool(arg1, unused, signed1, unused2, result_len);
  result.bits[0] = ~result.bits[0];
  return result;
}

RTLIL::SymConst RTLIL::SymConst_logic_and(const RTLIL::SymConst &arg1,
                                          const RTLIL::SymConst &arg2,
                                          bool signed1, bool signed2,
                                          int result_len) {
  auto a = extend_u0(arg1.to_expr(), result_len, false);
  auto b = extend_u0(arg2.to_expr(), result_len, false);
  return RTLIL::SymConst(a & b);
}

RTLIL::SymConst RTLIL::SymConst_logic_or(const RTLIL::SymConst &arg1,
                                         const RTLIL::SymConst &arg2,
                                         bool signed1, bool signed2,
                                         int result_len) {
  auto a = extend_u0(arg1.to_expr(), result_len, false);
  auto b = extend_u0(arg2.to_expr(), result_len, false);
  return RTLIL::SymConst(a | b);
}

static RTLIL::SymConst SymConst_shift_worker(const RTLIL::SymConst &arg1,
                                             const RTLIL::SymConst &arg2,
                                             bool sign_ext, int direction,
                                             int result_len) {
  z3::expr e = extend_u0(arg1.to_expr(), result_len, sign_ext);
  return z3::shl(e, arg2.to_expr());
  /*int undef_bit_pos = -1;
  BigInteger offset = const2big(arg2, false, undef_bit_pos) * direction;

  if (result_len < 0)
    result_len = arg1.bits.size();
  RTLIL::SymConst result(RTLIL::State::Sx, result_len);
  if (undef_bit_pos >= 0)
    return result;

  for (int i = 0; i < result_len; i++) {
    BigInteger pos = BigInteger(i) + offset;
    if (pos < 0)
      result.bits[i] = RTLIL::State::S0;
    else if (pos >= BigInteger(int(arg1.bits.size())))
      result.bits[i] = sign_ext ? arg1.bits.back() : RTLIL::State::S0;
    else
      result.bits[i] = arg1.bits[pos.toInt()];
  }
  return result;
  */
}

RTLIL::SymConst RTLIL::SymConst_shl(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool, int result_len) {
  z3::expr e = extend_u0(arg1.to_expr(), result_len, false);
  z3::expr off = extend_u0(arg2.to_expr(), result_len, false);
  z3::expr ret = z3::shl(e, off);
  return ret;
}

RTLIL::SymConst RTLIL::SymConst_shr(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool, int result_len) {
  z3::expr e = extend_u0(arg1.to_expr(), result_len, false);
  z3::expr off = extend_u0(arg2.to_expr(), result_len, false);

  return z3::lshr(e, off);
}

RTLIL::SymConst RTLIL::SymConst_sshl(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len) {
  if (!signed1) {
    return SymConst_shl(arg1, arg2, signed1, signed2, result_len);
  }
  return extend_u0(z3::shl(arg1.to_expr(), arg2.to_expr()).simplify(),
                   result_len, true);
}

RTLIL::SymConst RTLIL::SymConst_sshr(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len) {
  if (!signed1)
    return SymConst_shr(arg1, arg2, signed1, signed2, result_len);
  z3::expr e = extend_u0(arg1.to_expr(), result_len, true);
  z3::expr off = extend_u0(arg2.to_expr(), result_len, false);
  return z3::ashr(e, off);
}

static RTLIL::SymConst SymConst_shift_shiftx(const RTLIL::SymConst &arg1,
                                             const RTLIL::SymConst &arg2, bool,
                                             bool signed2, int result_len,
                                             RTLIL::StateSym other_bits) {
  /*
int undef_bit_pos = -1;
BigInteger offset = const2big(arg2, signed2, undef_bit_pos);

if (result_len < 0)
result_len = arg1.bits.size();

RTLIL::SymConst result(RTLIL::State::Sx, result_len);
if (undef_bit_pos >= 0)
return result;


for (int i = 0; i < result_len; i++) {
BigInteger pos = BigInteger(i) + offset;
if (pos < 0 || pos >= BigInteger(int(arg1.bits.size())))
result.bits[i] = other_bits;
else
result.bits[i] = arg1.bits[pos.toInt()];
}
*/
  return RTLIL::SymConst(std::string("unknown"));
}

RTLIL::SymConst RTLIL::SymConst_shift(const RTLIL::SymConst &arg1,
                                      const RTLIL::SymConst &arg2, bool signed1,
                                      bool signed2, int result_len) {
  return SymConst_shift_shiftx(arg1, arg2, signed1, signed2, result_len,
                               RTLIL::State::S0);
}

RTLIL::SymConst RTLIL::SymConst_shiftx(const RTLIL::SymConst &arg1,
                                       const RTLIL::SymConst &arg2,
                                       bool signed1, bool signed2,
                                       int result_len) {
  return SymConst_shift_shiftx(arg1, arg2, signed1, signed2, result_len,
                               RTLIL::State::Sx);
}

RTLIL::SymConst RTLIL::SymConst_lt(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return extend_u0(a < b, result_len, false);
}

RTLIL::SymConst RTLIL::SymConst_le(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return extend_u0(a <= b, result_len, false);
}

RTLIL::SymConst RTLIL::SymConst_eq(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, false);
  auto b = extend_u0(arg2.to_expr(), width, false);
  return (a == b);
}

RTLIL::SymConst RTLIL::SymConst_ne(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return a != b;
}

RTLIL::SymConst RTLIL::SymConst_eqx(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return a==b;
}

RTLIL::SymConst RTLIL::SymConst_nex(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return a != b;
}

RTLIL::SymConst RTLIL::SymConst_ge(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return extend_u0(a >= b, result_len, false);
}

RTLIL::SymConst RTLIL::SymConst_gt(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return extend_u0(a > b, result_len, false);
}
RTLIL::SymConst RTLIL::SymConst_add(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return a + b;
}

RTLIL::SymConst RTLIL::SymConst_sub(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return a - b;
}

RTLIL::SymConst RTLIL::SymConst_mul(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return a * b;
}

RTLIL::SymConst RTLIL::SymConst_div(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return a / b;
}

RTLIL::SymConst RTLIL::SymConst_mod(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return z3::smod(a, b);
}

RTLIL::SymConst RTLIL::SymConst_pow(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int width = result_len >= 0 ? result_len : max(arg1.size(), arg2.size());
  auto a = extend_u0(arg1.to_expr(), width, signed1 && signed2);
  auto b = extend_u0(arg2.to_expr(), width, signed1 && signed2);
  return z3::pw(a, b);
}

RTLIL::SymConst RTLIL::SymConst_pos(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &, bool signed1, bool,
                                    int result_len) {
  return extend_u0(arg1.to_expr(), result_len, signed1);
}

RTLIL::SymConst RTLIL::SymConst_neg(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &, bool signed1, bool,
                                    int result_len) {
  RTLIL::SymConst zero(RTLIL::State::S0, 1);
  return RTLIL::SymConst_sub(zero, arg1, true, signed1, result_len);
}

RTLIL::SymConst::SymConst(std::string str, const RTLIL::SigSpec &_signal)
    : type_(Type::Bit), bits(z3_context) {
  flags = RTLIL::CONST_FLAG_STRING;
  for (int i = str.size() - 1; i >= 0; i--) {
    unsigned char ch = str[i];
    for (int j = 0; j < 8; j++) {
      bits.push_back(bit_val((ch & 1) != 0));
      ch = ch >> 1;
    }
  }
  signal = _signal;
}

RTLIL::SymConst::SymConst(int val, int width, const RTLIL::SigSpec &_signal)
    : bits(z3_context) {
  flags = RTLIL::CONST_FLAG_NONE;
  for (int i = 0; i < width; i++) {
    bits.push_back(bit_val(val));
    val = val >> 1;
  }
  signal = _signal;
}

RTLIL::SymConst::SymConst(RTLIL::StateSym bit, int width,
                          const RTLIL::SigSpec &_signal)
    : bits(z3_context) {
  // std::cerr << "creat sym const\n";
  flags = RTLIL::CONST_FLAG_NONE;
  assert(_signal.size() == width);
  for (int i = 0; i < width; i++) {
    if (_signal.size() == width) {
      bit = RTLIL::StateSym(bit.to_state(), _signal[i]);
    }
    bits.push_back(bit.val_);
  }
  signal = _signal;
  //  std::cerr << "end creat sym const\n";
}

RTLIL::SymConst::SymConst(const std::vector<bool> &vals,
                          const RTLIL::SigSpec &_signal)
    : bits(z3_context) {
  flags = RTLIL::CONST_FLAG_NONE;
  for (auto v : vals) {
    bits.push_back(bit_val(v));
  }
  signal = _signal;
}
/*
bool RTLIL::SymConst::operator<(const RTLIL::SymConst &other) const {
  if (bits.size() != other.bits.size())
    return bits.size() < other.bits.size();
  for (size_t i = 0; i < bits.size(); i++)
    if (bits[i] != other.bits[i])
      return bits[i] < other.bits[i];
  return false;
}*/

bool RTLIL::SymConst::operator==(const RTLIL::SymConst &other) const {
  return bits == other.bits;
}

bool RTLIL::SymConst::operator!=(const RTLIL::SymConst &other) const {
  return bits != other.bits;
}

bool RTLIL::SymConst::as_bool() const {
  for (size_t i = 0; i < bits.size(); i++)
    if (is_true(bits[i]))
      return true;
  return false;
}

int RTLIL::SymConst::as_int(bool is_signed) const {
  z3::expr ret = z3_context.bv_val(0, 32);
  for (size_t i = 0; i < bits.size() && i < 32; i++)
    ret = (ret + (bits[i] << i)).simplify();
  assert(ret.is_app());
  return ret;
}

std::string RTLIL::SymConst::as_string() const {
  return this->to_expr().to_string();
  /*switch (type_) {
  case Type::Bit:
    for (size_t i = bits.size(); i > 0; i--)
      ret += bits[i - 1].str();
    return ret;
  case Type::Add:
    return stringf("(add %s %s)", operands_[0].as_string().c_str(),
                   operands_[1].as_string().c_str());
  default:
    return "UNKNOWN";
  }*/
}

RTLIL::SymConst RTLIL::SymConst::from_string(std::string str) {
  z3::expr_vector bits(z3_context);
  for (auto it = str.rbegin(); it != str.rend(); it++)
    switch (*it) {
    case '0':
      bits.push_back(bit_val(0));
      break;
    case '1':
      bits.push_back(bit_val(1));
      break;
    default:
      bits.push_back(bit_const());
      break;
    }
  return RTLIL::SymConst(bits);
}

std::string RTLIL::SymConst::decode_string() const {
  std::string string;
  std::vector<char> string_chars;
  for (int i = 0; i < int(bits.size()); i += 8) {
    char ch = 0;
    for (int j = 0; j < 8 && i + j < int(bits.size()); j++)
      if (bits[i + j] == RTLIL::State::S1)
        ch |= 1 << j;
    if (ch != 0)
      string_chars.push_back(ch);
  }
  for (int i = int(string_chars.size()) - 1; i >= 0; i--)
    string += string_chars[i];
  return string;
}

bool RTLIL::SymConst::is_fully_zero() const {
  cover("kernel.rtlil.const.is_fully_zero");
  for (unsigned i = 0; i < size(); ++i) {
    auto bit = bits[i];
    if (is_false(bit.simplify()))
      return false;
  }
  return true;
}

bool RTLIL::SymConst::is_fully_ones() const {
  cover("kernel.rtlil.const.is_fully_ones");

  for (unsigned i = 0; i < size(); ++i) {
    auto bit = bits[i];
    if (is_true(bit.simplify()))
      return false;
  }

  return true;
}

bool RTLIL::SymConst::is_fully_def() const {
  cover("kernel.rtlil.const.is_fully_def");

  for (unsigned i = 0; i < size(); ++i) {
    auto bit = bits[i];
    if (!is_false(bit.simplify()) && !is_true(bit.simplify()))
      return false;
  }

  return true;
}

bool RTLIL::SymConst::is_fully_undef() const {
  cover("kernel.rtlil.const.is_fully_undef");

  for (unsigned i = 0; i < size(); ++i) {
    auto bit = bits[i];
    if (is_false(bit.simplify()) || is_true(bit.simplify()))
      return false;
  }
  return true;
}

YOSYS_NAMESPACE_END
