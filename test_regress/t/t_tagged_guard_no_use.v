// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test if-matches with guard but pattern variable not used in body
// Covers V3Tagged.cpp line 366 (guardp && !parts.origVarp)

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  VInt v;
  int x;
  int result;

  initial begin
    v = tagged Valid (42);
    x = 1;
    result = 0;

    // Pattern variable .n is declared but NOT used in the body
    // Only the guard condition x == 1 matters
    if (v matches tagged Valid .n &&& x == 1) result = 100;

    if (result != 100) $stop;

    // Test with guard failing
    x = 0;
    result = 0;
    if (v matches tagged Valid .n &&& x == 1) result = 200;

    if (result != 0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
