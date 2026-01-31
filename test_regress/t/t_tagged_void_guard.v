// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test void pattern with guard expression
// Exercises void member handling in V3Tagged

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v;
  int x;

  initial begin
    x = 1;
    v = tagged Invalid;
    if (v matches tagged Invalid &&& (x > 0))
      $display("void with guard");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
