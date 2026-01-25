// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test guard expression with else clause
// Exercises guard-with-else branch in V3LinkParse

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v;

  initial begin
    v = tagged Valid (42);
    if (v matches tagged Valid .n &&& (n > 100))
      $stop;
    else
      $display("else taken");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
