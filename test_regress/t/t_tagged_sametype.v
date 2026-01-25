// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test multiple identical tagged union declarations
// Exercises sameNode() comparison in V3AstNodes

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  typedef union tagged { void Invalid; int Valid; } VInt2;  // Identical structure
  VInt v1;
  VInt2 v2;

  initial begin
    v1 = tagged Valid (42);
    v2 = tagged Valid (42);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
