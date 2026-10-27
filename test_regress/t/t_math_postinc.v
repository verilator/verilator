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

  // Method calls are linked late, so their arguments are only linked after V3LinkInc
  class Sink;
    int got;
    function void set(int v);
      got = v;
    endfunction
  endclass
  Sink sink;

  // Lvalues with ++/-- in their indices
  typedef struct {int v;} s_t;
  class Holder;
    int m[4];
  endclass
  Holder holder;
  int idx;
  int arr4[4];
  logic [7:0] bits8;
  s_t sarr[3];
  int arr2d[3][2];

  // ++/-- in static variable initializers, which run in an unspecified order
  int sinit;
  class StaticInit;
    static int s = sinit++;
    int m = sinit++;
  endclass
  StaticInit staticInit;
  function int fStaticInit();
    static int s = sinit++;
    return s;
  endfunction
  function automatic int faStaticInit();
    static int s = sinit++;
    return s;
  endfunction

  // ++/-- in default argument values
  int dflt;
  class DefaultArg;
    function int m(int v = dflt++);
      return v;
    endfunction
    static function int s(int v = --dflt);
      return v;
    endfunction
  endclass
  DefaultArg defaultArg;
  function int fDefaultArg(int v = dflt--);
    return v;
  endfunction
  function automatic int faDefaultArg(int v = ++dflt);
    return v;
  endfunction

  // Recursion while the temporary holding the result of n-- is still live
  function automatic int sum(int n);
    return n == 0 ? 0 : n-- + sum(n);
  endfunction

  // Impure (side-effecting) function for use as a short-circuit LHS
  function automatic int bump();
    side = side + 1;
    return 1;
  endfunction
  function automatic int postSide();
    return side++;
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

    // ---- Constant LHS of && / || ----
    a = 4;  if (0 && a++ < 10) begin end  `checkh(a, 4);
    a = 4;  if (1 || a-- < 10) begin end  `checkh(a, 4);

    // ---- ?: evaluates only the selected branch ----
    a = 1;  b = 5;  c = (a > 0) ? a++ : --b;  `checkh(c, 1);  `checkh(a, 2);  `checkh(b, 5);
    a = 0;  b = 5;  c = (a > 0) ? a++ : --b;  `checkh(c, 4);  `checkh(a, 0);  `checkh(b, 4);
    a = 0;  b = 5;  c = (a++ > 0) ? a++ + 10 : b-- + 20;
    `checkh(c, 25);  `checkh(a, 1);  `checkh(b, 4);

    // ---- ?: nested in && ----
    a = 1;  b = 5;  if (a == 1 && ((a > 0 ? a++ : --b) > 0)) begin end
    `checkh(a, 2);  `checkh(b, 5);

    // ---- -> with true antecedent ----
    a = 1;  b = 5;  if ((a > 0) -> (++b > 0)) c = 1; else c = 0;  `checkh(c, 1);  `checkh(b, 6);

    // ---- ++/-- in && / || inside a function (function-local temp) ----
    `checkh(f_and(5), 6);    // 5>0 true, post-inc runs -> 6
    `checkh(f_and(0), 0);    // 0>0 false, short-circuit -> unchanged
    `checkh(f_or(5), 5);    // 5>0 true, short-circuit -> unchanged
    `checkh(f_or(0), 1);    // 0>0 false, post-inc runs -> 1
    `checkh(f_single(4), 1005); // 4==4 (once) && 4<100 -> taken=1, x=5
    `checkh(f_single(6), 6);  // 6==4 false, short-circuit -> taken=0, x=6

    // ---- ++/-- in a recursive function ----
    `checkh(sum(4), 10);

    // ---- ++/-- in an lvalue index is evaluated once ----
    idx = 0;  arr4 = '{0, 0, 0, 0};  arr4[idx++] = 5;  `checkh(idx, 1);  `checkh(arr4[0], 5);
    idx = 2;  bits8 = 0;  bits8[idx++ +: 2] = 2'b11;  `checkh(idx, 3);  `checkh(bits8, 8'h0c);
    idx = 1;  sarr[idx++].v = 7;  `checkh(idx, 2);  `checkh(sarr[1].v, 7);
    idx = 2;  arr2d = '{'{0, 0}, '{0, 0}, '{0, 0}};  arr2d[idx++][1] += 3;
    `checkh(idx, 3);  `checkh(arr2d[2][1], 3);
    idx = 0;  arr4[idx++] <= 9;  `checkh(idx, 1);
    idx = 0;  arr4[0] = 1;  bits8 = 8'hff;  {arr4[idx++], bits8} += 1;
    `checkh(idx, 1);  `checkh(arr4[0], 2);  `checkh(bits8, 8'h00);
    // Nested in the operand of ++/--
    side = 0;  arr2d = '{'{0, 0}, '{0, 0}, '{0, 0}};  arr2d[postSide() + 1][postSide()]++;
    `checkh(side, 2);  `checkh(arr2d[1][1], 1);
    side = 0;  arr4[1] = 4;  b = arr4[bump()]++;
    `checkh(side, 1);  `checkh(b, 4);  `checkh(arr4[1], 5);
    idx = 1;  arr4[1] = 10;  b = arr4[idx++]++;
    `checkh(idx, 2);  `checkh(b, 10);  `checkh(arr4[1], 11);
    holder = new;  idx = 0;  holder.m[idx++]++;  `checkh(idx, 1);  `checkh(holder.m[0], 1);
    idx = 0;  b = holder.m[idx++]++;  `checkh(idx, 1);  `checkh(b, 1);  `checkh(holder.m[0], 2);

    // ---- ++/-- in an intra-assignment delay ----
    // verilator lint_off ZERODLY
    idx = 0;  b = 1;  arr4[idx++] = #(b++) 5;
    `checkh(idx, 1);  `checkh(b, 2);  `checkh(arr4[0], 5);
    arr4[idx++] <= #(b--) 6;  `checkh(idx, 2);  `checkh(b, 1);
    // verilator lint_on ZERODLY
    #3;  `checkh(arr4[1], 6);

    // ---- ++/-- in a method call argument ----
    sink = new;
    a = 7;  sink.set(a++);  `checkh(sink.got, 7);  `checkh(a, 8);
    a = 7;  sink.set(--a);  `checkh(sink.got, 6);  `checkh(a, 6);

    // ---- ++/-- in static variable initializers ----
    a = StaticInit::s + fStaticInit() + faStaticInit();  `checkh(a, 3);  `checkh(sinit, 3);
    staticInit = new;  `checkh(staticInit.m, 3);  `checkh(sinit, 4);

    // ---- ++/-- in default argument values ----
    dflt = 5;
    a = fDefaultArg();  `checkh(a, 5);  `checkh(dflt, 4);
    a = fDefaultArg(9);  `checkh(a, 9);  `checkh(dflt, 4);
    a = faDefaultArg();  `checkh(a, 5);  `checkh(dflt, 5);
    defaultArg = new;
    a = defaultArg.m();  `checkh(a, 5);  `checkh(dflt, 6);
    a = DefaultArg::s();  `checkh(a, 5);  `checkh(dflt, 5);

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
