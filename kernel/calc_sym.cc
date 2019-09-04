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
#include "z3.h"
#include "libs/bigint/BigIntegerLibrary.hh"
#include <string>
YOSYS_NAMESPACE_BEGIN
z3::context z3_context;
static void extend_u0(RTLIL::SymConst &arg, int width, bool is_signed) {
  RTLIL::StateSym padding = RTLIL::State::S0;

  if (arg.bits.size() > 0 && is_signed)
    padding = arg.bits.back();

  while (int(arg.bits.size()) < width)
    arg.bits.push_back(padding);

  arg.bits.resize(width);
}

static BigInteger const2big(const RTLIL::SymConst &val, bool as_signed,
                            int &undef_bit_pos) {
  BigUnsigned mag;

  BigInteger::Sign sign = BigInteger::positive;
  State inv_sign_bit = RTLIL::State::S1;
  size_t num_bits = val.bits.size();

  if (as_signed && num_bits && val.bits[num_bits - 1] == RTLIL::State::S1) {
    inv_sign_bit = RTLIL::State::S0;
    sign = BigInteger::negative;
    num_bits--;
  }

  for (size_t i = 0; i < num_bits; i++)
    if (val.bits[i] == RTLIL::State::S0 || val.bits[i] == RTLIL::State::S1)
      mag.setBit(i, val.bits[i] == inv_sign_bit);
    else if (undef_bit_pos < 0)
      undef_bit_pos = i;

  if (sign == BigInteger::negative)
    mag += 1;

  return BigInteger(mag, sign);
}

static RTLIL::SymConst big2const(const BigInteger &val, int result_len,
                                 int undef_bit_pos) {
  if (undef_bit_pos >= 0)
    return RTLIL::SymConst(RTLIL::State::Sx, result_len);

  BigUnsigned mag = val.getMagnitude();
  RTLIL::SymConst result(0, result_len);

  if (!mag.isZero()) {
    if (val.getSign() < 0) {
      mag--;
      for (int i = 0; i < result_len; i++)
        result.bits[i] = mag.getBit(i) ? RTLIL::State::S0 : RTLIL::State::S1;
    } else {
      for (int i = 0; i < result_len; i++)
        result.bits[i] = mag.getBit(i) ? RTLIL::State::S1 : RTLIL::State::S0;
    }
  }

#if 0
	if (undef_bit_pos >= 0)
		for (int i = undef_bit_pos; i < result_len; i++)
			result.bits[i] = RTLIL::State::Sx;
#endif

  return result;
}

static RTLIL::StateSym logic_and(const RTLIL::StateSym &a,
                                 const RTLIL::StateSym &b) {
  if (a == RTLIL::State::S0)
    return RTLIL::State::S0;
  if (b == RTLIL::State::S0)
    return RTLIL::State::S0;
  if (a == RTLIL::State::S1 && b != RTLIL::State::S1)
    return RTLIL::State::S1;
  if (a == RTLIL::State::S1)
    return b;
  if (b == RTLIL::State::S1)
    return a;
  return RTLIL::StateSym ::CreateAnd(vector<RTLIL::StateSym>({a, b}));
}

static RTLIL::StateSym logic_or(const RTLIL::StateSym &a,
                                const RTLIL::StateSym &b) {
  if (a == RTLIL::State::S1)
    return RTLIL::State::S1;
  if (b == RTLIL::State::S1)
    return RTLIL::State::S1;
  if (a == RTLIL::State::S0 && b != RTLIL::State::S0)
    return RTLIL::State::S0;
  if (a == RTLIL::State::S0)
    return b;
  if (b == RTLIL::State::S0)
    return a;
  return RTLIL::StateSym ::CreateOr(vector<RTLIL::StateSym>({a, b}));
}

static RTLIL::StateSym logic_xor(const RTLIL::StateSym &a,
                                 const RTLIL::StateSym &b) {
  if (a.is_const() && b.is_const())
    return a.val_ != b.val_ ? RTLIL::State::S1 : RTLIL::State::S0;
  if (a == RTLIL::State::S0)
    return b;
  if (a == RTLIL::State::S1)
    return RTLIL::StateSym ::CreateNot(b);
  if (b == RTLIL::State::S0)
    return a;
  if (b == RTLIL::State::S1)
    return RTLIL::StateSym ::CreateNot(a);
  return RTLIL::StateSym ::CreateXor(vector<RTLIL::StateSym>({a, b}));
}
static RTLIL::StateSym logic_not(const RTLIL::StateSym &a) {
  if (a.is_const())
    return (a.val_ == RTLIL::State::S1) ? RTLIL::State::S0 : RTLIL::State::S1;
  return RTLIL::StateSym ::CreateNot(a);
}
static RTLIL::StateSym logic_xnor(const RTLIL::StateSym &a,
                                  const RTLIL::StateSym &b) {
  if (a.is_const() && b.is_const())
    return a.val_ == b.val_ ? RTLIL::State::S1 : RTLIL::State::S0;
  if (a == RTLIL::State::S1)
    return b;
  if (a == RTLIL::State::S0)
    return RTLIL::StateSym ::CreateNot(b);
  if (b == RTLIL::State::S1)
    return a;
  if (b == RTLIL::State::S0)
    return RTLIL::StateSym ::CreateNot(a);
  return RTLIL::StateSym ::CreateNot(
      RTLIL::StateSym::CreateXor(vector<RTLIL::StateSym>({a, b})));
}

RTLIL::SymConst RTLIL::SymConst_not(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &, bool signed1, bool,
                                    int result_len) {
  if (result_len < 0)
    result_len = arg1.bits.size();

  RTLIL::SymConst arg1_ext = arg1;
  extend_u0(arg1_ext, result_len, signed1);

  RTLIL::SymConst result(RTLIL::State::Sx, result_len);
  for (size_t i = 0; i < size_t(result_len); i++) {
    if (i >= arg1_ext.bits.size())
      result.bits[i] = RTLIL::State::S0;
    else if (arg1_ext.bits[i] == RTLIL::State::S0)
      result.bits[i] = RTLIL::State::S1;
    else if (arg1_ext.bits[i] == RTLIL::State::S1)
      result.bits[i] = RTLIL::State::S0;
    else {
      result.bits[i] = RTLIL::StateSym ::CreateNot(arg1_ext.bits[i]);
    }
  }

  return result;
}

static RTLIL::SymConst
logic_wrapper(RTLIL::StateSym (*logic_func)(const RTLIL::StateSym &,
                                            const RTLIL::StateSym &),
              RTLIL::SymConst arg1, RTLIL::SymConst arg2, bool signed1,
              bool signed2, int result_len = -1) {
  if (result_len < 0)
    result_len = max(arg1.bits.size(), arg2.bits.size());

  extend_u0(arg1, result_len, signed1);
  extend_u0(arg2, result_len, signed2);

  RTLIL::SymConst result(RTLIL::State::Sx, result_len);
  for (size_t i = 0; i < size_t(result_len); i++) {
    RTLIL::StateSym a = i < arg1.bits.size() ? arg1.bits[i] : RTLIL::State::S0;
    RTLIL::StateSym b = i < arg2.bits.size() ? arg2.bits[i] : RTLIL::State::S0;
    result.bits[i] = logic_func(a, b);
  }

  return result;
}

RTLIL::SymConst RTLIL::SymConst_and(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  return logic_wrapper(logic_and, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::SymConst RTLIL::SymConst_or(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  return logic_wrapper(logic_or, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::SymConst RTLIL::SymConst_xor(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  return logic_wrapper(logic_xor, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::SymConst RTLIL::SymConst_xnor(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len) {
  return logic_wrapper(logic_xnor, arg1, arg2, signed1, signed2, result_len);
}

static RTLIL::SymConst
logic_reduce_wrapper(RTLIL::StateSym initial,
                     RTLIL::StateSym (*logic_func)(const RTLIL::StateSym &,
                                                   const RTLIL::StateSym &),
                     const RTLIL::SymConst &arg1, int result_len) {
  RTLIL::StateSym temp = initial;

  for (size_t i = 0; i < arg1.bits.size(); i++)
    temp = logic_func(temp, arg1.bits[i]);

  RTLIL::SymConst result(temp);
  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  return result;
}

RTLIL::SymConst RTLIL::SymConst_reduce_and(const RTLIL::SymConst &arg1,
                                           const RTLIL::SymConst &, bool, bool,
                                           int result_len) {
  return logic_reduce_wrapper(RTLIL::State::S1, logic_and, arg1, result_len);
}

RTLIL::SymConst RTLIL::SymConst_reduce_or(const RTLIL::SymConst &arg1,
                                          const RTLIL::SymConst &, bool, bool,
                                          int result_len) {
  return logic_reduce_wrapper(RTLIL::State::S0, logic_or, arg1, result_len);
}

RTLIL::SymConst RTLIL::SymConst_reduce_xor(const RTLIL::SymConst &arg1,
                                           const RTLIL::SymConst &, bool, bool,
                                           int result_len) {
  return logic_reduce_wrapper(RTLIL::State::S0, logic_xor, arg1, result_len);
}

RTLIL::SymConst RTLIL::SymConst_reduce_xnor(const RTLIL::SymConst &arg1,
                                            const RTLIL::SymConst &, bool, bool,
                                            int result_len) {
  RTLIL::SymConst buffer =
      logic_reduce_wrapper(RTLIL::State::S0, logic_xor, arg1, result_len);
  if (!buffer.bits.empty()) {
    if (buffer.bits.front() == RTLIL::State::S0)
      buffer.bits.front() = RTLIL::State::S1;
    else if (buffer.bits.front() == RTLIL::State::S1)
      buffer.bits.front() = RTLIL::State::S0;
  }
  return buffer;
}

RTLIL::SymConst RTLIL::SymConst_reduce_bool(const RTLIL::SymConst &arg1,
                                            const RTLIL::SymConst &, bool, bool,
                                            int result_len) {
  return logic_reduce_wrapper(RTLIL::State::S0, logic_or, arg1, result_len);
}

RTLIL::SymConst RTLIL::SymConst_logic_not(const RTLIL::SymConst &arg1,
                                          const RTLIL::SymConst &, bool signed1,
                                          bool, int result_len) {
  int undef_bit_pos_a = -1;
  BigInteger a = const2big(arg1, signed1, undef_bit_pos_a);
  RTLIL::SymConst result(
      a.isZero()
          ? undef_bit_pos_a >= 0
                ? RTLIL::StateSym ::CreateNot(
                      SymConst_reduce_or(arg1, arg1, 0, 0, 1).bits.front())
                : RTLIL::State::S1
          : RTLIL::State::S0);
  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  return result;
}

RTLIL::SymConst RTLIL::SymConst_logic_and(const RTLIL::SymConst &arg1,
                                          const RTLIL::SymConst &arg2,
                                          bool signed1, bool signed2,
                                          int result_len) {
  int undef_bit_pos_a = -1, undef_bit_pos_b = -1;
  BigInteger a = const2big(arg1, signed1, undef_bit_pos_a);
  BigInteger b = const2big(arg2, signed2, undef_bit_pos_b);

  RTLIL::StateSym bit_a =
      a.isZero() ? undef_bit_pos_a >= 0 ? RTLIL::State::Sx : RTLIL::State::S0
                 : RTLIL::State::S1;
  RTLIL::StateSym bit_b =
      b.isZero() ? undef_bit_pos_b >= 0 ? RTLIL::State::Sx : RTLIL::State::S0
                 : RTLIL::State::S1;

  RTLIL::SymConst result(
      logic_and(SymConst_reduce_or(arg1, arg1, 0, 0, 1).bits.front(),
                SymConst_reduce_or(arg2, arg2, 0, 0, 1).bits.front()));

  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  return result;
}

RTLIL::SymConst RTLIL::SymConst_logic_or(const RTLIL::SymConst &arg1,
                                         const RTLIL::SymConst &arg2,
                                         bool signed1, bool signed2,
                                         int result_len) {
  int undef_bit_pos_a = -1, undef_bit_pos_b = -1;
  BigInteger a = const2big(arg1, signed1, undef_bit_pos_a);
  BigInteger b = const2big(arg2, signed2, undef_bit_pos_b);

  RTLIL::StateSym bit_a =
      a.isZero() ? undef_bit_pos_a >= 0 ? RTLIL::State::Sx : RTLIL::State::S0
                 : RTLIL::State::S1;
  RTLIL::StateSym bit_b =
      b.isZero() ? undef_bit_pos_b >= 0 ? RTLIL::State::Sx : RTLIL::State::S0
                 : RTLIL::State::S1;
  RTLIL::SymConst result(logic_or(bit_a, bit_b));

  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  return result;
}

static RTLIL::SymConst SymConst_shift_worker(const RTLIL::SymConst &arg1,
                                             const RTLIL::SymConst &arg2,
                                             bool sign_ext, int direction,
                                             int result_len) {
  int undef_bit_pos = -1;
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
}

RTLIL::SymConst RTLIL::SymConst_shl(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool, int result_len) {
  RTLIL::SymConst arg1_ext = arg1;
  extend_u0(arg1_ext, result_len, signed1);
  return SymConst_shift_worker(arg1_ext, arg2, false, -1, result_len);
}

RTLIL::SymConst RTLIL::SymConst_shr(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool, int result_len) {
  RTLIL::SymConst arg1_ext = arg1;
  extend_u0(arg1_ext, max(result_len, GetSize(arg1)), signed1);
  return SymConst_shift_worker(arg1_ext, arg2, false, +1, result_len);
}

RTLIL::SymConst RTLIL::SymConst_sshl(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len) {
  if (!signed1)
    return SymConst_shl(arg1, arg2, signed1, signed2, result_len);
  return SymConst_shift_worker(arg1, arg2, true, -1, result_len);
}

RTLIL::SymConst RTLIL::SymConst_sshr(const RTLIL::SymConst &arg1,
                                     const RTLIL::SymConst &arg2, bool signed1,
                                     bool signed2, int result_len) {
  if (!signed1)
    return SymConst_shr(arg1, arg2, signed1, signed2, result_len);
  return SymConst_shift_worker(arg1, arg2, true, +1, result_len);
}

static RTLIL::SymConst SymConst_shift_shiftx(const RTLIL::SymConst &arg1,
                                             const RTLIL::SymConst &arg2, bool,
                                             bool signed2, int result_len,
                                             RTLIL::StateSym other_bits) {
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

  return result;
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
  int undef_bit_pos = -1;
  bool y = const2big(arg1, signed1, undef_bit_pos) <
           const2big(arg2, signed2, undef_bit_pos);
  RTLIL::SymConst result(undef_bit_pos >= 0
                             ? RTLIL::StateSym ::CreateLt(vector<StateSym>())
                             : y ? RTLIL::State::S1 : RTLIL::State::S0);

  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  return result;
}

RTLIL::SymConst RTLIL::SymConst_le(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int undef_bit_pos = -1;
  bool y = const2big(arg1, signed1, undef_bit_pos) <=
           const2big(arg2, signed2, undef_bit_pos);
  RTLIL::SymConst result(undef_bit_pos >= 0
                             ? RTLIL::State::Sx
                             : y ? RTLIL::State::S1 : RTLIL::State::S0);

  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  return result;
}

RTLIL::SymConst RTLIL::SymConst_eq(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  RTLIL::SymConst arg1_ext = arg1;
  RTLIL::SymConst arg2_ext = arg2;
  RTLIL::SymConst result(RTLIL::State::S0, result_len);

  int width = max(arg1_ext.bits.size(), arg2_ext.bits.size());
  extend_u0(arg1_ext, width, signed1 && signed2);
  extend_u0(arg2_ext, width, signed1 && signed2);

  RTLIL::StateSym matched_status = RTLIL::State::S1;
  for (size_t i = 0; i < arg1_ext.bits.size(); i++) {
    if (arg1_ext.bits.at(i) == RTLIL::State::S0 &&
        arg2_ext.bits.at(i) == RTLIL::State::S1)
      return result;
    if (arg1_ext.bits.at(i) == RTLIL::State::S1 &&
        arg2_ext.bits.at(i) == RTLIL::State::S0)
      return result;
    if (!arg1_ext.bits.at(i).is_const() || !arg2_ext.bits.at(i).is_const())
      matched_status = logic_and(
          matched_status,
          RTLIL::StateSym::CreateEq(arg1_ext.bits.at(i), arg2_ext.bits.at(i)));
  }

  result.bits.front() = matched_status;
  return result;
}

RTLIL::SymConst RTLIL::SymConst_ne(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  RTLIL::SymConst result =
      RTLIL::SymConst_eq(arg1, arg2, signed1, signed2, result_len);
  if (result.bits.front() == RTLIL::State::S0)
    result.bits.front() = RTLIL::State::S1;
  else if (result.bits.front() == RTLIL::State::S1)
    result.bits.front() = RTLIL::State::S0;
  return result;
}

RTLIL::SymConst RTLIL::SymConst_eqx(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  RTLIL::SymConst arg1_ext = arg1;
  RTLIL::SymConst arg2_ext = arg2;
  RTLIL::SymConst result(RTLIL::State::S0, result_len);

  int width = max(arg1_ext.bits.size(), arg2_ext.bits.size());
  extend_u0(arg1_ext, width, signed1 && signed2);
  extend_u0(arg2_ext, width, signed1 && signed2);

  for (size_t i = 0; i < arg1_ext.bits.size(); i++) {
    if (arg1_ext.bits.at(i) != arg2_ext.bits.at(i))
      return result;
  }

  result.bits.front() = RTLIL::State::S1;
  return result;
}

RTLIL::SymConst RTLIL::SymConst_nex(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  RTLIL::SymConst result =
      RTLIL::SymConst_eqx(arg1, arg2, signed1, signed2, result_len);
  if (result.bits.front() == RTLIL::State::S0)
    result.bits.front() = RTLIL::State::S1;
  else if (result.bits.front() == RTLIL::State::S1)
    result.bits.front() = RTLIL::State::S0;
  return result;
}

RTLIL::SymConst RTLIL::SymConst_ge(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  log("SymConst_get %d: %s %s\n", result_len, arg1.as_string().c_str(),
      arg2.as_string().c_str());
  int undef_bit_pos = -1;
  bool y = const2big(arg1, signed1, undef_bit_pos) >=
           const2big(arg2, signed2, undef_bit_pos);
  RTLIL::SymConst result(undef_bit_pos >= 0
                             ? RTLIL::State::Sx
                             : y ? RTLIL::State::S1 : RTLIL::State::S0);

  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  return result;
}

RTLIL::SymConst RTLIL::SymConst_gt(const RTLIL::SymConst &arg1,
                                   const RTLIL::SymConst &arg2, bool signed1,
                                   bool signed2, int result_len) {
  int undef_bit_pos = -1;
  bool y = const2big(arg1, signed1, undef_bit_pos) >
           const2big(arg2, signed2, undef_bit_pos);
  RTLIL::SymConst result(undef_bit_pos >= 0
                             ? RTLIL::State::Sx
                             : y ? RTLIL::State::S1 : RTLIL::State::S0);
  /*log("1. SymConst_gt %d: %s %s=> %s: %d\n", result_len,
      arg1.as_string().c_str(), arg2.as_string().c_str(),
      result.as_string().c_str(), GetSize(result));*/
  while (int(result.bits.size()) < result_len)
    result.bits.push_back(RTLIL::State::S0);
  /*log("SymConst_gt %d: %s %s=> %s: %d\n", result_len, arg1.as_string().c_str(),
      arg2.as_string().c_str(), result.as_string().c_str(), GetSize(result));*/
  return result;
}
RTLIL::SymConst RTLIL::SymConst_add(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  log("add\n");
   vector<StateSym> bits(result_len, State::S0);
    log("add %d\n", result_len);
    StateSym c = State::S0;
    StateSym cc = State::S0;
    for (size_t i = 0; i < result_len; ++i) {
      StateSym a = (i < arg1.bits.size()) ? arg1.bits[i] : State::S0;
      StateSym b = (i < arg2.bits.size()) ? arg2.bits[i] : State::S0;
      c = cc;
      if (c == State::S0) {
        cc = logic_and(a, b);
        bits[i] = logic_xor(a, b);
      } else if (c == State::S1) {
        cc = logic_or(a, b);
        bits[i] = logic_xnor(a, b);
      } else {
        cc = logic_or(logic_and(logic_not(c), logic_or(a, b)),
                      logic_and(c, logic_and(a, b)));
        bits[i] = logic_or(logic_and(logic_not(c), logic_xor(a, b)),
                           logic_and(c, logic_xnor(a, b)));
      }
    }
    return RTLIL::SymConst(bits);
	}
RTLIL::SymConst SymConst_add_low(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  log("add\n");
  int undef_bit_pos = -1;
  BigInteger y = const2big(arg1, signed1, undef_bit_pos) +
                 const2big(arg2, signed2, undef_bit_pos);
  if (undef_bit_pos > 0) {
    RTLIL::SymConst::CreateAdd(arg1, arg2);
  }
  return big2const(
      y, result_len >= 0 ? result_len : max(arg1.bits.size(), arg2.bits.size()),
      undef_bit_pos);
}
// see sym_calc.cc for the implementation of this functions
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

RTLIL::SymConst RTLIL::SymConst_sub(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int undef_bit_pos = -1;
  BigInteger y = const2big(arg1, signed1, undef_bit_pos) -
                 const2big(arg2, signed2, undef_bit_pos);
  return big2const(
      y, result_len >= 0 ? result_len : max(arg1.bits.size(), arg2.bits.size()),
      undef_bit_pos);
}

RTLIL::SymConst RTLIL::SymConst_mul(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int undef_bit_pos = -1;
  BigInteger y = const2big(arg1, signed1, undef_bit_pos) *
                 const2big(arg2, signed2, undef_bit_pos);
  return big2const(
      y, result_len >= 0 ? result_len : max(arg1.bits.size(), arg2.bits.size()),
      min(undef_bit_pos, 0));
}

RTLIL::SymConst RTLIL::SymConst_div(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int undef_bit_pos = -1;
  BigInteger a = const2big(arg1, signed1, undef_bit_pos);
  BigInteger b = const2big(arg2, signed2, undef_bit_pos);
  if (b.isZero())
    return RTLIL::SymConst(RTLIL::State::Sx, result_len);
  bool result_neg = (a.getSign() == BigInteger::negative) !=
                    (b.getSign() == BigInteger::negative);
  a = a.getSign() == BigInteger::negative ? -a : a;
  b = b.getSign() == BigInteger::negative ? -b : b;
  return big2const(result_neg ? -(a / b) : (a / b),
                   result_len >= 0 ? result_len
                                   : max(arg1.bits.size(), arg2.bits.size()),
                   min(undef_bit_pos, 0));
}

RTLIL::SymConst RTLIL::SymConst_mod(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int undef_bit_pos = -1;
  BigInteger a = const2big(arg1, signed1, undef_bit_pos);
  BigInteger b = const2big(arg2, signed2, undef_bit_pos);
  if (b.isZero())
    return RTLIL::SymConst(RTLIL::State::Sx, result_len);
  bool result_neg = a.getSign() == BigInteger::negative;
  a = a.getSign() == BigInteger::negative ? -a : a;
  b = b.getSign() == BigInteger::negative ? -b : b;
  return big2const(result_neg ? -(a % b) : (a % b),
                   result_len >= 0 ? result_len
                                   : max(arg1.bits.size(), arg2.bits.size()),
                   min(undef_bit_pos, 0));
}

RTLIL::SymConst RTLIL::SymConst_pow(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &arg2, bool signed1,
                                    bool signed2, int result_len) {
  int undef_bit_pos = -1;

  BigInteger a = const2big(arg1, signed1, undef_bit_pos);
  BigInteger b = const2big(arg2, signed2, undef_bit_pos);
  BigInteger y = 1;

  if (a == 0 && b < 0)
    return RTLIL::SymConst(RTLIL::State::Sx, result_len);

  if (a == 0 && b > 0)
    return RTLIL::SymConst(RTLIL::State::S0, result_len);

  if (b < 0) {
    if (a < -1 || a > 1)
      y = 0;
    if (a == -1)
      y = (-b % 2) == 0 ? 1 : -1;
  }

  if (b > 0) {
    // Power-modulo with 2^result_len as modulus
    BigInteger modulus = 1;
    int modulus_bits = (result_len >= 0 ? result_len : 1024);
    for (int i = 0; i < modulus_bits; i++)
      modulus *= 2;

    bool flip_result_sign = false;
    if (a < 0) {
      a *= -1;
      if (b % 2 == 1)
        flip_result_sign = true;
    }

    while (b > 0) {
      if (b % 2 == 1)
        y = (y * a) % modulus;
      b = b / 2;
      a = (a * a) % modulus;
    }

    if (flip_result_sign)
      y *= -1;
  }

  return big2const(
      y, result_len >= 0 ? result_len : max(arg1.bits.size(), arg2.bits.size()),
      min(undef_bit_pos, 0));
}

RTLIL::SymConst RTLIL::SymConst_pos(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &, bool signed1, bool,
                                    int result_len) {
  RTLIL::SymConst arg1_ext = arg1;
  extend_u0(arg1_ext, result_len, signed1);

  return arg1_ext;
}

RTLIL::SymConst RTLIL::SymConst_neg(const RTLIL::SymConst &arg1,
                                    const RTLIL::SymConst &, bool signed1, bool,
                                    int result_len) {
  RTLIL::SymConst arg1_ext = arg1;
  RTLIL::SymConst zero(RTLIL::State::S0, 1);

  return RTLIL::SymConst_sub(zero, arg1_ext, true, signed1, result_len);
}

RTLIL::SymConst::SymConst() : type_(Type::Bit) {
  flags = RTLIL::CONST_FLAG_NONE;
}

RTLIL::SymConst::SymConst(std::string str, const RTLIL::SigSpec &_signal)
    : type_(Type::Bit) {
  flags = RTLIL::CONST_FLAG_STRING;
  for (int i = str.size() - 1; i >= 0; i--) {
    unsigned char ch = str[i];
    for (int j = 0; j < 8; j++) {
      bits.push_back((ch & 1) != 0 ? RTLIL::S1 : RTLIL::S0);
      ch = ch >> 1;
    }
  }
  signal = _signal;
}

RTLIL::SymConst::SymConst(int val, int width, const RTLIL::SigSpec &_signal) {
  flags = RTLIL::CONST_FLAG_NONE;
  for (int i = 0; i < width; i++) {
    bits.push_back((val & 1) != 0 ? RTLIL::S1 : RTLIL::S0);
    val = val >> 1;
  }
  signal = _signal;
}

RTLIL::SymConst::SymConst(RTLIL::StateSym bit, int width,
                          const RTLIL::SigSpec &_signal) {
  flags = RTLIL::CONST_FLAG_NONE;
  for (int i = 0; i < width; i++)
    bits.push_back(bit);
  signal = _signal;
}

RTLIL::SymConst::SymConst(const std::vector<bool> &bits,
                          const RTLIL::SigSpec &_signal) {
  flags = RTLIL::CONST_FLAG_NONE;
  for (auto b : bits)
    this->bits.push_back(b ? RTLIL::S1 : RTLIL::S0);
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
    if (bits[i] == RTLIL::S1)
      return true;
  return false;
}

int RTLIL::SymConst::as_int(bool is_signed) const {
  int32_t ret = 0;
  for (size_t i = 0; i < bits.size() && i < 32; i++)
    if (bits[i] == RTLIL::S1)
      ret |= 1 << i;
  if (is_signed && bits.back() == RTLIL::S1)
    for (size_t i = bits.size(); i < 32; i++)
      ret |= 1 << i;
  return ret;
}

std::string RTLIL::SymConst::as_string() const {
  std::string ret;
  z3::expr_vector exprs(bits.front().val_.ctx());
  for(auto b : bits){
    exprs.push_back(b.val_);
  }
  return z3::concat(exprs).simplify().to_string();
  switch (type_) {
  case Type::Bit:
    for (size_t i = bits.size(); i > 0; i--)
      ret += bits[i - 1].str();
    return ret;
  case Type::Add:
    return stringf("(add %s %s)", operands_[0].as_string().c_str(),
                   operands_[1].as_string().c_str());
  default:
    return "UNKNOWN";
  }
}

RTLIL::SymConst RTLIL::SymConst::from_string(std::string str) {
  SymConst c;
  for (auto it = str.rbegin(); it != str.rend(); it++)
    switch (*it) {
    case '0':
      c.bits.push_back(State::S0);
      break;
    case '1':
      c.bits.push_back(State::S1);
      break;
    case 'x':
      c.bits.push_back(State::Sx);
      break;
    case 'z':
      c.bits.push_back(State::Sz);
      break;
    case 'm':
      c.bits.push_back(State::Sm);
      break;
    default:
      c.bits.push_back(State::Sa);
    }
  return c;
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

  for (auto bit : bits)
    if (bit != RTLIL::State::S0)
      return false;

  return true;
}

bool RTLIL::SymConst::is_fully_ones() const {
  cover("kernel.rtlil.const.is_fully_ones");

  for (auto bit : bits)
    if (bit != RTLIL::State::S1)
      return false;

  return true;
}

bool RTLIL::SymConst::is_fully_def() const {
  cover("kernel.rtlil.const.is_fully_def");

  for (auto bit : bits)
    if (bit != RTLIL::State::S0 && bit != RTLIL::State::S1)
      return false;

  return true;
}

bool RTLIL::SymConst::is_fully_undef() const {
  cover("kernel.rtlil.const.is_fully_undef");

  for (auto bit : bits)
    if (bit != RTLIL::State::Sx && bit != RTLIL::State::Sz)
      return false;

  return true;
}

YOSYS_NAMESPACE_END
