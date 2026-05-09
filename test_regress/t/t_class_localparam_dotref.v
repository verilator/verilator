// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Tests reference into a parameterized class via :: in a parameter expression.

virtual class C #(
    parameter int a = 0
);
  localparam int b = a;
  static function int get_a();
    return a;
  endfunction
  typedef enum {
    E0 = 100,
    E1 = 101
  } e_t;
endclass

class D #(
    parameter int v = C#(7)::b
);
  static function int get_v();
    return v;
  endfunction
endclass

typedef C#(0) inst0;
typedef C#(1) inst1;
typedef C#(4) chain_a;
typedef chain_a chain_b;

module t (  /*AUTOARG*/);

  // Wilson's exact case: typedef-aliased paramed class lparam.
  localparam int LP_TYPEDEF_LPARAM = inst0::b;

  // Direct (no typedef) paramed class lparam.
  localparam int LP_DIRECT_LPARAM = C#(2)::b;

  // Static method RHS via typedef.
  localparam int LP_STATIC_FUNC = inst1::get_a();

  // Enum value RHS, direct and typedef-aliased.
  localparam int LP_ENUM_DIRECT = int'(C#(3)::E0);
  localparam int LP_ENUM_TYPEDEF = int'(inst0::E1);

  // Override propagation: explicit value should reach the lparam.
  localparam int LP_OVERRIDE = C#(7)::a;

  // Compile-time math inside the class parameterization.
  localparam int LP_MATH = C#(2 + 3)::a;

  // Module localparam used as the class parameter.
  localparam int P = 5;
  localparam int LP_PARAM_DRIVES_PARAM = C#(P)::a;

  // Chained typedef alias: typedef A B; B::b should resolve through both.
  localparam int LP_CHAIN_TYPEDEF = chain_b::b;

  // Multiple Dots in one expression with different specializations.
  localparam int LP_MULTI = C#(0)::a + C#(1)::a + C#(2)::a;

  // Class param default itself uses a paramed-class Dot, then we read v.
  localparam int LP_CLASS_DEFAULT = D#()::get_v();

  // Nested: paramed-class Dot used as the explicit parameter to another paramed class.
  localparam int LP_NESTED_ARG = D#(C#(9)::b)::get_v();

  // Typedef-aliased paramed class as inner of nested arg (silent-miscompile risk).
  typedef C#(13) c13;
  localparam int LP_NESTED_TYPEDEF_INNER = D#(c13::b)::get_v();

  // 3-level nesting via lparam access: D's v gets D#(C#(15)::b), then read v.
  localparam int LP_THREE_LEVEL = D#(D#(C#(15)::b)::v)::get_v();

  // Chained typedef alias of a typedef of a paramed class.
  typedef c13 c13_alias;
  localparam int LP_CHAINED_TYPEDEF_INNER = D#(c13_alias::b)::get_v();

  initial begin
    `checkd(LP_TYPEDEF_LPARAM, 0);
    `checkd(LP_DIRECT_LPARAM, 2);
    `checkd(LP_STATIC_FUNC, 1);
    `checkd(LP_ENUM_DIRECT, 100);
    `checkd(LP_ENUM_TYPEDEF, 101);
    `checkd(LP_OVERRIDE, 7);
    `checkd(LP_MATH, 5);
    `checkd(LP_PARAM_DRIVES_PARAM, 5);
    `checkd(LP_CHAIN_TYPEDEF, 4);
    `checkd(LP_MULTI, 3);
    `checkd(LP_CLASS_DEFAULT, 7);
    `checkd(LP_NESTED_ARG, 9);
    `checkd(LP_NESTED_TYPEDEF_INNER, 13);
    `checkd(LP_THREE_LEVEL, 15);
    `checkd(LP_CHAINED_TYPEDEF_INNER, 13);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
