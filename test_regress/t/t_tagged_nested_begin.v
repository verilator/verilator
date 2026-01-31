// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test pattern matching with named nested begin blocks
// This exercises the matchesVarName() suffix matching code path in V3Tagged

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v;
  int result;

  initial begin : outer
    begin : inner
      v = tagged Valid (42);
      if (v matches tagged Valid .n) result = n;
    end
    if (result != 42) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
