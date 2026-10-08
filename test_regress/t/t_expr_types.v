// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkt(exp, result) \
  do \
    if ($typename(exp) !== $typename(result)) begin \
      $write("%s !== %s\n", $typename(exp), $typename(result)); \
      `stop; \
    end \
  while(0)

`define checkopt(lhs, op, rhs, result) \
  do \
    if ($typename((lhs) op (rhs)) !== $typename(result)) begin \
      $write("((%s) %s (%s)) !== %s - it is %s\n", $typename(lhs), `"op`", $typename(rhs), $typename(result), $typename((lhs) op (rhs))); \
      `stop; \
    end \
  while(0)

`define checkcond(cond, then_value, else_value, result) \
  do \
    if ($typename((cond) ? (then_value) : (else_value)) !== $typename(result)) begin \
      $write("(%s) ? (%s) : (%s) !== %s - it is %s\n", $typename(cond), $typename(then_value), $typename(else_value), $typename(result), $typename((cond) ? (then_value) : (else_value))); \
      `stop; \
    end \
  while(0)

`define checkt_result_or(op) \
  do begin \
    `checkopt(b, op, b, b); \
    `checkopt(b, op, l, l); \
    `checkopt(l, op, b, l); \
    `checkopt(l, op, l, l); \
  end while(0)

`define checkUniopSameT(op) \
  do begin \
    `checkt(op b, b); \
    `checkt(op l, l); \
  end while(0)

`ifdef VERILATOR
// The '$c(1)' is there to prevent inlining of the signal by V3Gate.
`define IMPURE_ONE ($c(1))
`else
// Use standard $random. The chance of getting 2 consecutive zeroes is negligible.
`define IMPURE_ONE (|($random | $random))
`endif
// verilog_format: on

typedef enum bit [2:0] {E2_A, E2_B} enum2_t;
typedef enum logic [2:0] {E4_A, E4_B} enum4_t;
typedef struct {
  bit [6:0] member;
} struct_t;
typedef struct packed {
  bit [6:0] member;
} packed_struct_t;

class Base;
endclass

class Derived extends Base;
endclass

module t;
  initial begin
    automatic bit b;
    automatic logic l;
    automatic bit signed [31:0] i2;
    automatic logic signed [31:0] i4;
    automatic byte byte_var;
    automatic bit unsigned [31:0] ub;
    automatic logic unsigned [31:0] ul;
    automatic bit [1:0] bit2;
    automatic logic [1:0] logic2;
    automatic bit [2:0] bit3;
    automatic bit [14:0] bit15;
    automatic logic [2:0] logic3;
    automatic logic [14:0] logic15;
    automatic bit [5:0] bit6;
    automatic logic [5:0] logic6;
    automatic bit [6:0] bit7;
    automatic logic [6:0] logic7;
    automatic bit [63:0] bit64;
    automatic logic [63:0] logic64;
    automatic bit [127:0] bit128;
    automatic logic [127:0] logic128;
    automatic enum2_t e2a = E2_A;
    automatic enum2_t e2b = E2_B;
    automatic enum4_t e4a = E4_A;
    automatic enum4_t e4b = E4_B;
    automatic real r;
    automatic string s;
    automatic struct_t st1;
    automatic struct_t st2;
    automatic packed_struct_t packed_st1;
    automatic packed_struct_t packed_st2;
    automatic packed_struct_t packed_st3;
    automatic bit queue1[$];
    automatic bit queue2[$];
    automatic Base base_h;
    automatic Derived derived_h;

    b = `IMPURE_ONE;
    l = `IMPURE_ONE;
    i2 = `IMPURE_ONE;
    i4 = `IMPURE_ONE;
    ub = `IMPURE_ONE;
    ul = `IMPURE_ONE;

    `checkt_result_or(==);
    `checkt_result_or(!=);
    `checkt_result_or(>=);
    `checkt_result_or(<=);
    `checkt_result_or(>);
    `checkt_result_or(<);

    `checkopt(b, ===, b, b);
    `checkopt(b, ===, l, b);
    `checkopt(l, ===, b, b);
    `checkopt(l, ===, l, b);
    `checkopt(b, !==, b, b);
    `checkopt(b, !==, l, b);
    `checkopt(l, !==, b, b);
    `checkopt(l, !==, l, b);

    `checkopt(b, ==?, b, b);
    `checkopt(b, ==?, l, b);
    `checkopt(l, ==?, b, l);
    `checkopt(l, ==?, l, l);
    `checkopt(b, !=?, b, b);
    `checkopt(b, !=?, l, b);
    `checkopt(l, !=?, b, l);
    `checkopt(l, !=?, l, l);

    `checkt_result_or(&&);
    `checkt_result_or(||);
    `checkt_result_or(->);
    `checkt_result_or(<->);

    `checkt_result_or(&);
    `checkt_result_or(|);
    `checkt_result_or(^);
    `checkt_result_or(~^);
    `checkt_result_or(^~);

    `checkt_result_or(+);
    `checkt_result_or(-);
    `checkt_result_or(*);

    `checkopt(b, /, b, l);
    `checkopt(b, /, l, l);
    `checkopt(l, /, b, l);
    `checkopt(l, /, l, l);

    `checkopt(i2, /, 0, i4);
    `checkopt(i4, /, 0, i4);
    `checkopt(i2, /, 1, i2);
    `checkopt(i4, /, 1, i4);

    `checkopt(b, %, b, l);
    `checkopt(b, %, l, l);
    `checkopt(l, %, b, l);
    `checkopt(l, %, l, l);

    `checkopt(i2, %, 0, i4);
    `checkopt(i4, %, 0, i4);
    `checkopt(i2, %, 1, i2);
    `checkopt(i4, %, 1, i4);

    `checkopt(i2, **, i2, i4);
    `checkopt(i2, **, i4, i4);
    `checkopt(i4, **, i2, i4);
    `checkopt(i4, **, i4, i4);

    `checkopt(2, **, i2, i2);
    `checkopt(2, **, i4, i4);
    `checkopt(0, **, i2, i4);
    `checkopt(0, **, i4, i4);

    `checkopt(i2, **, -1, i4);
    `checkopt(i2, **, 1, i2);
    `checkopt(i4, **, 1, i4);
    `checkopt(i4, **, -1, i4);

    `checkopt(ub, **, i2, ul);
    `checkopt(ub, **, i4, ul);
    `checkopt(ul, **, i2, ul);
    `checkopt(ul, **, i4, ul);

    `checkopt(i2, **, ub, i2);
    `checkopt(i2, **, ul, i4);
    `checkopt(i4, **, ub, i4);
    `checkopt(i4, **, ul, i4);

    `checkopt(2, **, ub, i2);
    `checkopt(2, **, ul, i4);
    `checkopt(0, **, ub, i2);
    `checkopt(0, **, ul, i4);

    `checkopt(ub, **, ub, ub);
    `checkopt(ub, **, ul, ul);
    `checkopt(ul, **, ub, ul);
    `checkopt(ul, **, ul, ul);

    `checkt_result_or(>>);
    `checkt_result_or(<<);
    `checkt_result_or(>>>);
    `checkt_result_or(<<<);

    `checkUniopSameT(|);
    `checkUniopSameT(&);
    `checkUniopSameT(^);
    `checkUniopSameT(+);
    `checkUniopSameT(-);
    `checkUniopSameT(~);
    `checkUniopSameT(!);
    `checkUniopSameT(~^);
    `checkUniopSameT(^~);
    `checkUniopSameT(~|);
    `checkUniopSameT(~&);

    `checkcond(b, b, b, b);
    `checkcond(b, b, l, l);
    `checkcond(b, l, b, l);
    `checkcond(b, l, l, l);
    `checkcond(l, b, b, l);
    `checkcond(l, b, l, l);
    `checkcond(l, l, b, l);
    `checkcond(l, l, l, l);

    `checkcond(b, i2, ub, ub);
    `checkcond(b, ub, i2, ub);
    `checkcond(b, 1, byte_var, i2);
    `checkcond(b, byte_var, 1, i2);
    `checkcond(l, bit15, bit15, logic15);

    `checkcond(b, e2a, e2b, e2a);
    `checkcond(l, e2a, e2b, logic3);
    `checkcond(b, e4a, e4b, e4a);
    `checkcond(l, e4a, e4b, e4a);

    `checkcond(b, r, b, r);
    `checkcond(b, b, r, r);
    `checkcond(b, s, "", s);
    `checkcond(b, "", s, s);

    `checkcond(b, st1, st2, st1);
    `checkcond(l, packed_st1, packed_st2, packed_st1);
    packed_st3 = l ? packed_st1 : packed_st2;
    `checkcond(b, b, queue1, queue2);
    `checkcond(b, queue1, b, queue2);

    `checkcond(b, null, null, null);
    `checkcond(b, base_h, derived_h, base_h);
    `checkcond(b, derived_h, base_h, base_h);
    `checkcond(b, null, derived_h, derived_h);
    `checkcond(b, derived_h, null, derived_h);

    `checkt(({b}), b);
    `checkt(({l}), l);
    `checkt(({b, b}), bit2);
    `checkt(({b, l}), logic2);
    `checkt(({l, b}), logic2);
    `checkt(({l, l}), logic2);
    `checkt(({b, b, b}), bit3);
    `checkt(({b, l, b}), logic3);
    `checkt(({i2, i2}), bit64);
    `checkt(({i4, i2}), logic64);

    `checkt(({3{b}}), bit3);
    `checkt(({3{l}}), logic3);
    `checkt(({3{b, b}}), bit6);
    `checkt(({3{b, l}}), logic6);
    `checkt(({3{l, b}}), logic6);
    `checkt(({3{l, l}}), logic6);
    `checkt(({2{i2, ub}}), bit128);
    `checkt(({2{i4, ub}}), logic128);
    `checkt(({b, {0{l}}}), b);
    `checkt(({{0{l}}, b}), b);

    `checkt(({s, ""}), s);
    `checkt(({2{s}}), s);

    `checkt(bit15[0], b);
    `checkt(logic15[0], l);
    `checkt(bit15[6:0], bit7);
    `checkt(logic15[6:0], logic7);
    `checkt(bit15[0 +: 7], bit7);
    `checkt(logic15[0 +: 7], logic7);
    `checkt(bit15[14 -: 7], bit7);
    `checkt(logic15[14 -: 7], logic7);

    `checks($typename($time), "time");
    `checks($typename($timeprecision), "integer");
    // even though `time` is four-state, `$time` always returns a value from a two-state domain,
    // therefore it should be treated as a two-state value
    `checkopt($time, ==, 1, b);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
