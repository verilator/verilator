// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test pattern matching inside begin blocks
// This exercises the searchStmtsForVar() code path in V3Tagged

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v;

  initial begin
    begin  // Pattern var inside begin block triggers searchStmtsForVar()
      v = tagged Valid (42);
      if (v matches tagged Valid .n)
        if (n != 42) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
