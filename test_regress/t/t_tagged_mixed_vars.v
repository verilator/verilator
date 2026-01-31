// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test pattern matching with mixed variables in body
// Covers V3Tagged.cpp line 168 false branch (VarRef doesn't match pattern var)

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v;
  int counter, result;

  initial begin
    v = tagged Valid (10);
    counter = 5;

    // if-matches: body has both pattern var 'n' and unrelated var 'counter'
    // When replacing VarRefs, 'counter' triggers line 168 false branch
    if (v matches tagged Valid .n)
      result = counter + n;

    if (result != 15) $stop;

    // case-matches: body has both pattern var 'x' and unrelated var 'counter'
    result = 0;
    case (v) matches
      tagged Invalid: result = counter;
      tagged Valid .x: result = counter * x;
    endcase

    if (result != 50) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
