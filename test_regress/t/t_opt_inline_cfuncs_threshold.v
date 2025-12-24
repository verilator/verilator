// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test module to exercise threshold checking in CFunc inlining
// With low thresholds, these functions should NOT be inlined
module t;
  reg [31:0] a, b, c, d, e, f, g, h;

  initial begin
    // Multiple operations to create larger CFuncs
    a = 32'd1;
    b = 32'd2;
    c = a + b;
    d = c * 2;
    e = d - 1;
    f = e + a;
    g = f * b;
    h = g + c + d + e + f;

    if (h != 32'd32) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
