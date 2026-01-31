// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test chained matches expressions with &&& guards
// This exercises the backp() chain fix in buildInnerBody()

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v1, v2;
  int result;

  initial begin
    v1 = tagged Valid (10);
    v2 = tagged Valid (20);

    // Chained matches with &&& guard
    if (v1 matches tagged Valid .a &&& v2 matches tagged Valid .b)
      result = a + b;
    if (result != 30) $stop;

    // Test with one invalid
    v1 = tagged Invalid;
    result = 0;
    if (v1 matches tagged Valid .a &&& v2 matches tagged Valid .b)
      result = a + b;
    if (result != 0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
