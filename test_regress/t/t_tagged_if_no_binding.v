// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test if-matches with TaggedExpr (no variable binding)
// Covers V3Tagged.cpp lines 621-622

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

    // if-matches with no binding - creates AstTaggedExpr not AstTaggedPattern
    if (v matches tagged Valid) result = 1;

    if (result != 1) $stop;

    v = tagged Invalid;
    result = 0;

    if (v matches tagged Invalid) result = 2;

    if (result != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
