// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test empty bodies in pattern matching constructs
// Exercises empty body branches in V3LinkParse

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v;

  initial begin
    v = tagged Valid (42);
    // Empty if-matches body
    if (v matches tagged Valid .n) ;
    // Empty case-matches body
    case (v) matches
      tagged Valid .n: ;
      default: ;
    endcase
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
