// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Tests reference into a parameterized class via :: in a parameter expression.

virtual class C #(parameter int a = 0);
  localparam int b = a;
  static function int get_a();
    return a;
  endfunction
  typedef enum {E0 = 100, E1 = 101} e_t;
endclass

class D #(parameter int v = C#(7)::b);
  static function int get_v();
    return v;
  endfunction
endclass

typedef C#(0) inst0;
typedef C#(1) inst1;
typedef C#(4) chain_a;
typedef chain_a chain_b;

module t (/*AUTOARG*/);

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
    if (LP_TYPEDEF_LPARAM !== 0) begin $write("%%Error: TYPEDEF_LPARAM=%0d\n", LP_TYPEDEF_LPARAM); $stop; end
    if (LP_DIRECT_LPARAM !== 2) begin $write("%%Error: DIRECT_LPARAM=%0d\n", LP_DIRECT_LPARAM); $stop; end
    if (LP_STATIC_FUNC !== 1) begin $write("%%Error: STATIC_FUNC=%0d\n", LP_STATIC_FUNC); $stop; end
    if (LP_ENUM_DIRECT !== 100) begin $write("%%Error: ENUM_DIRECT=%0d\n", LP_ENUM_DIRECT); $stop; end
    if (LP_ENUM_TYPEDEF !== 101) begin $write("%%Error: ENUM_TYPEDEF=%0d\n", LP_ENUM_TYPEDEF); $stop; end
    if (LP_OVERRIDE !== 7) begin $write("%%Error: OVERRIDE=%0d\n", LP_OVERRIDE); $stop; end
    if (LP_MATH !== 5) begin $write("%%Error: MATH=%0d\n", LP_MATH); $stop; end
    if (LP_PARAM_DRIVES_PARAM !== 5) begin $write("%%Error: PARAM_DRIVES_PARAM=%0d\n", LP_PARAM_DRIVES_PARAM); $stop; end
    if (LP_CHAIN_TYPEDEF !== 4) begin $write("%%Error: CHAIN_TYPEDEF=%0d\n", LP_CHAIN_TYPEDEF); $stop; end
    if (LP_MULTI !== 3) begin $write("%%Error: MULTI=%0d\n", LP_MULTI); $stop; end
    if (LP_CLASS_DEFAULT !== 7) begin $write("%%Error: CLASS_DEFAULT=%0d\n", LP_CLASS_DEFAULT); $stop; end
    if (LP_NESTED_ARG !== 9) begin $write("%%Error: NESTED_ARG=%0d\n", LP_NESTED_ARG); $stop; end
    if (LP_NESTED_TYPEDEF_INNER !== 13) begin $write("%%Error: NESTED_TYPEDEF_INNER=%0d\n", LP_NESTED_TYPEDEF_INNER); $stop; end
    if (LP_THREE_LEVEL !== 15) begin $write("%%Error: THREE_LEVEL=%0d\n", LP_THREE_LEVEL); $stop; end
    if (LP_CHAINED_TYPEDEF_INNER !== 13) begin $write("%%Error: CHAINED_TYPEDEF_INNER=%0d\n", LP_CHAINED_TYPEDEF_INNER); $stop; end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
