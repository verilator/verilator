// DESCRIPTION: Verilator: Verilog Test module
//
// Test inline pre/post increment/decrement operators, including
// inside logical operators (&&, ||) with short-circuit semantics.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  integer a, b, c;
  reg cond;
  int side;

  // Impure (side-effecting) function for use as a short-circuit LHS
  function automatic int bump();
    side = side + 1;
    return 1;
  endfunction

  // ++/-- in && / || inside a function/task exercises the function-local temp
  function automatic int f_and(int x);
    if (x > 0 && x++ < 100) ;
    return x;
  endfunction
  function automatic int f_or(int x);
    if (x > 0 || x++ < 100) ;
    return x;
  endfunction
  // LHS reads the gated variable; must see the pre-increment value exactly once
  function automatic int f_single(int x);
    int taken = 0;
    if (x == 4 && x++ < 100) taken = 1;
    return taken * 1000 + x;
  endfunction

  initial begin
    // ---- Basic post/pre increment/decrement ----
    a = 5;  b = a++;        `checkh(b, 5);  `checkh(a, 6);
    a = 5;  b = ++a;        `checkh(a, 6);  `checkh(b, 6);
    a = 10;  b = 5;  b = a++ + b; `checkh(b, 15); `checkh(a, 11);
    a = 10;  b = 5;  b = ++a + b; `checkh(b, 16); `checkh(a, 11);
    a = 7;  b = a++ * 2;      `checkh(b, 14);  `checkh(a, 8);
    a = 7;  b = ++a * 2;      `checkh(b, 16);  `checkh(a, 8);
    a = 3;  b = 4;  c = a++ + b++; `checkh(c, 7);  `checkh(a, 4); `checkh(b, 5);
    a = 3;  b = 4;  c = ++a + ++b; `checkh(c, 9);  `checkh(a, 4); `checkh(b, 5);
    a = 10;  b = 3;  c = a++ - b--; `checkh(c, 7);  `checkh(a, 11); `checkh(b, 2);
    a = 5;  b = 5;  b = a--;    `checkh(b, 5);  `checkh(a, 4);
    a = 5;  b = --a;          `checkh(b, 4);  `checkh(a, 4);

    // ---- Post-inc in shift (5 << 5 = 160) ----
    a = 5;  b = 5;  b = b << a++; `checkh(b, 160); `checkh(a, 6);

    // ---- Post-inc in paren expr ----
    a = 2;  b = (a++ + 1) * 3;    `checkh(b, 9);  `checkh(a, 3);

    // ---- Post-inc in while with && (constant) ----
    a = 0;  while (1 && a++ < 3) begin end `checkh(a, 4);

    // ---- Post-inc in while with && (variable cond, non-short-circuit) ----
    cond = 1;  a = 0;  while (cond && a++ < 3) begin end `checkh(a, 4);

    // ---- Post-inc in while with && (variable cond, short-circuit) ----
    cond = 0;  a = 0;  while (cond && a++ < 3) begin end `checkh(a, 0);

    // ---- Post-inc in while with || ----
    a = 0;  while (0 || a++ < 3) begin end `checkh(a, 4);

    // ---- && short-circuit ----
    a = 0;  if (0 && a++ < 3) begin end   `checkh(a, 0);

    // ---- && non-short-circuit ----
    a = 0;  if (1 && a++ < 5) begin end   `checkh(a, 1);

    // ---- || non-short-circuit ----
    a = 0;  if (0 || a++ < 5) begin end   `checkh(a, 1);

    // ---- || short-circuit ----
    a = 0;  if (1 || a++ < 5) begin end   `checkh(a, 0);

    // ---- Pre-inc with && ----
    a = 0;  if (1 && ++a < 5) begin end   `checkh(a, 1);

    // ---- Pre-inc short-circuit ----
    a = 0;  if (0 && ++a < 5) begin end   `checkh(a, 0);

    // ---- Pre-inc with || ----
    a = 0;  if (0 || ++a < 5) begin end   `checkh(a, 1);
    a = 0;  if (1 || ++a < 5) begin end   `checkh(a, 0);

    // ---- Nested && chain ----
    a = 0;  if (1 && 1 && a++ < 5) begin end `checkh(a, 1);

    // ---- Post-dec with && ----
    a = 5;  if (1 && a-- > 0) begin end   `checkh(a, 4);

    // ---- Pre-dec with && short-circuit ----
    a = 5;  if (0 && --a > 0) begin end   `checkh(a, 5);

    // ---- Post-dec with || ----
    a = 5;  if (0 || a-- > 0) begin end   `checkh(a, 4);
    a = 5;  if (1 || a-- > 0) begin end   `checkh(a, 5);

    // ---- Pre-dec with || ----
    a = 5;  if (0 || --a > 0) begin end   `checkh(a, 4);

    // ---- Multiple increments in && chain ----
    a = 0;  b = 0;
    if (1 && a++ < 5 && b++ < 5) begin end
    `checkh(a, 1);  `checkh(b, 1);

    // ---- Post-inc on left side of && ----
    a = 0;  if (a++ < 5 && 1) begin end   `checkh(a, 1);

    // ---- Post-inc on left side of || ----
    a = 0;  if (a++ < 5 || 0) begin end   `checkh(a, 1);

    // ---- Pre-inc on left side of || ----
    a = 0;  if (++a < 5 || 0) begin end   `checkh(a, 1);

    // ---- Mixed && and || with post-inc ----
    a = 0;  b = 0;
    if (1 && a++ < 5 || b++ < 5) begin end
    `checkh(a, 1);  `checkh(b, 0);

    a = 0;  b = 0;
    if (0 && a++ < 5 || b++ < 5) begin end
    `checkh(a, 0);  `checkh(b, 1);

    // ---- Deep nesting (3 levels &&) ----
    a = 0;  b = 0;  c = 0;
    if (1 && 1 && a++ < 5 && b++ < 5 && c++ < 5) begin end
    `checkh(a, 1);  `checkh(b, 1);  `checkh(c, 1);

    a = 0;  b = 0;  c = 0;
    if (1 && 0 && a++ < 5 && b++ < 5 && c++ < 5) begin end
    `checkh(a, 0);  `checkh(b, 0);  `checkh(c, 0);

    // ---- LHS reads variable that gated RHS ++/-- writes (single-eval) ----
    a = 4;  if (a == 4 && a++ < 10) begin end  `checkh(a, 5);
    a = 6;  if (a == 4 && a++ < 10) begin end  `checkh(a, 6);
    a = 0;  if (a < 1  && a++ < 5)  begin end  `checkh(a, 1);
    a = 5;  if (a > 0  && a-- > 0)  begin end  `checkh(a, 4);
    a = 4;  if (a == 4 && ++a < 10) begin end  `checkh(a, 5);

    // ---- || mirror: LHS reads variable that gated RHS modifies ----
    a = 4;  if (a != 4 || a++ < 10) begin end  `checkh(a, 5);
    a = 6;  if (a != 4 || a++ < 10) begin end  `checkh(a, 6);

    // ---- Nested gate: inner && with non-const LHS inside an outer gate ----
    a = 4;  if (a == 4 && (a < 10 && a++ < 20)) begin end  `checkh(a, 5);
    a = 20;  if (a == 20 && (a < 10 && a++ < 30)) begin end `checkh(a, 20);
    a = 0;  if (a == 4 && (a < 10 && a++ < 20)) begin end  `checkh(a, 0);

    // ---- ++/-- in && / || inside a function (function-local temp) ----
    `checkh(f_and(5), 6);    // 5>0 true, post-inc runs -> 6
    `checkh(f_and(0), 0);    // 0>0 false, short-circuit -> unchanged
    `checkh(f_or(5), 5);    // 5>0 true, short-circuit -> unchanged
    `checkh(f_or(0), 1);    // 0>0 false, post-inc runs -> 1
    `checkh(f_single(4), 1005); // 4==4 (once) && 4<100 -> taken=1, x=5
    `checkh(f_single(6), 6);  // 6==4 false, short-circuit -> taken=0, x=6

    // ---- Impure (side-effecting) LHS must be evaluated exactly once ----
    side = 0;  a = 0;  if (bump() > 0 && a++ < 5) begin end  `checkh(side, 1);  `checkh(a, 1);
    side = 0;  a = 0;  if (bump() < 0 && a++ < 5) begin end  `checkh(side, 1);  `checkh(a, 0);

    // ---- ++/-- on LHS, side-effecting function on opposite (RHS) side ----
    side = 0;  a = 0;  if (a++ < 5 && bump() > 0) begin end  `checkh(a, 1);  `checkh(side, 1);
    side = 0;  a = 0;  if (a++ > 5 && bump() > 0) begin end  `checkh(a, 1);  `checkh(side, 0);
    side = 0;  a = 0;  if (a++ > 5 || bump() > 0) begin end  `checkh(a, 1);  `checkh(side, 1);
    side = 0;  a = 0;  if (a++ < 5 || bump() > 0) begin end  `checkh(a, 1);  `checkh(side, 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
