// DESCRIPTION: Verilator: Test X/Z four-state simulation with larger bit widths (64/128/256-bit)
//
// This test verifies four-state simulation with larger bit widths.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;

  // 64-bit four-state signals
  reg [63:0] a64 = 64'hFEDC_BA98_7654_3210;
  reg [63:0] b64 = 64'h0123_4567_89AB_CDEF;
  reg [63:0] x64 = 64'hXXXX_XXXX_XXXX_XXXX;
  reg [63:0] z64 = 64'hZZZZ_ZZZZ_ZZZZ_ZZZZ;
  reg [63:0] xz64 = 64'hXZ10_XZ10_XZ10_XZ10;
  
  // 128-bit four-state signals
  reg [127:0] a128 = 128'hFEDC_BA98_7654_3210_0123_4567_89AB_CDEF;
  reg [127:0] b128 = 128'h0123_4567_89AB_CDEF_FEDC_BA98_7654_3210;
  reg [127:0] x128 = 128'hXXXXXXXXXXXXXXXXFFFFFFFFFFFFFFFF;
  reg [127:0] z128 = 128'hZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ;
  
  // 256-bit four-state signals
  reg [255:0] a256;
  reg [255:0] x256;
  reg [255:0] z256;
  
  // Results
  reg [63:0] res_and_64;
  reg [63:0] res_or_64;
  reg [63:0] res_xor_64;
  reg [63:0] res_add_64;
  reg [127:0] res_and_128;
  reg [127:0] res_or_128;
  reg [255:0] res_and_256;
  
  initial begin
    // Initialize 256-bit with pattern
    a256 = 256'hAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    x256 = 256'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
    x256[255:128] = 256'hXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX;
    z256 = 256'hZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ;
    
    // 64-bit operations with X/Z
    res_and_64 = a64 & x64;  // X & anything = X
    res_or_64 = b64 | z64;   // Z | anything = X
    res_xor_64 = x64 ^ xz64; // XOR with X = X
    res_add_64 = a64 + x64;  // Add with X = X
    
    // 128-bit operations with X/Z
    res_and_128 = a128 & x128;
    res_or_128 = b128 | z128;
    
    // 256-bit operations with X/Z
    res_and_256 = a256 & x256;
    
    $write("=== 64-bit Tests ===\n");
    $write("a64 = %h\n", a64);
    $write("b64 = %h\n", b64);
    $write("x64 = %b\n", x64);
    $write("z64 = %b\n", z64);
    $write("xz64 = %b\n", xz64);
    $write("a64 & x64 = %b (expect all X)\n", res_and_64);
    $write("b64 | z64 = %b (expect all X)\n", res_or_64);
    $write("x64 ^ xz64 = %b (expect all X)\n", res_xor_64);
    $write("a64 + x64 = %b (expect all X)\n", res_add_64);
    
    $write("\n=== 128-bit Tests ===\n");
    $write("a128[127:64] = %h\n", a128[127:64]);
    $write("x128 = %b\n", x128);
    $write("z128 = %b\n", z128);
    $write("a128 & x128 = %b (expect all X)\n", res_and_128);
    $write("b128 | z128 = %b (expect all X)\n", res_or_128);
    
    $write("\n=== 256-bit Tests ===\n");
    $write("a256[255:192] = %h\n", a256[255:192]);
    $write("x256[255:192] = %b\n", x256[255:192]);
    $write("z256[255:192] = %b\n", z256[255:192]);
    $write("a256 & x256 = %b (expect X in upper bits)\n", res_and_256);
    
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
