// DESCRIPTION: Verilator: Test X/Z four-state simulation with larger bit widths (64-bit)
//
// This test verifies four-state simulation with 64-bit operations.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;

  // 64-bit four-state signals
  reg [63:0] a64 = 64'hFEDC_BA98_7654_3210;
  reg [63:0] b64 = 64'h0123_4567_89AB_CDEF;
  reg [63:0] xz64 = 64'hXZ10_XZ10_XZ10_XZ10;
  
  // Results
  reg [63:0] res_and_64;
  reg [63:0] res_or_64;
  reg [63:0] res_xor_64;
  reg [63:0] res_not_64;
  
  initial begin
    // 64-bit operations with X/Z
    res_and_64 = a64 & xz64;  // X & anything = X
    res_or_64 = b64 | xz64;   // X | anything = X
    res_xor_64 = a64 ^ xz64;  // XOR with X = X
    res_not_64 = ~xz64;       // ~X = X, ~Z = X
    
    $write("=== 64-bit Tests ===\n");
    $write("a64 = %h\n", a64);
    $write("b64 = %h\n", b64);
    $write("xz64 = %b\n", xz64);
    $write("a64 & xz64 = %b\n", res_and_64);
    $write("b64 | xz64 = %b\n", res_or_64);
    $write("a64 ^ xz64 = %b\n", res_xor_64);
    $write("~xz64 = %b\n", res_not_64);
    
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
