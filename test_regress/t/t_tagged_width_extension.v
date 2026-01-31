// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged unions with mixed width members
// This exercises the width extension code path in V3Tagged transformTaggedExpr

module t;
  typedef union tagged {
    bit [7:0] Small;
    bit [31:0] Large;
  } MixedWidth;

  MixedWidth m;
  bit [7:0] result8;
  bit [31:0] result32;

  initial begin
    // Small member requires width extension to match Large member width
    m = tagged Small (8'hAB);
    if (m matches tagged Small .x) result8 = x;
    if (result8 != 8'hAB) $stop;

    m = tagged Large (32'hDEADBEEF);
    if (m matches tagged Large .y) result32 = y;
    if (result32 != 32'hDEADBEEF) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
