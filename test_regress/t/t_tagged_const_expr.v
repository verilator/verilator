// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test if-matches in context where V3Const would try to convert to ternary
// Covers V3Const.cpp containsMatches() check

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  VInt v;
  int result;

  initial begin
    v = tagged Valid (42);
    result = 0;

    // If-matches with simple assignments in both branches
    // V3Const would normally try to convert this to ternary
    // but containsMatches() should prevent that
    if (v matches tagged Valid .n)
      result = n;
    else
      result = -1;

    if (result != 42) $stop;

    // Another pattern
    v = tagged Invalid;
    if (v matches tagged Valid .n)
      result = n;
    else
      result = 99;

    if (result != 99) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
