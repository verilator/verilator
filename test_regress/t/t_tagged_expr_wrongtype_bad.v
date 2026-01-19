// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when tagged expression used with non-tagged union type

module t;
  // Regular (non-tagged) union with a named typedef
  typedef union packed {
    int a;
    int b;
  } non_tagged_union_t;

  non_tagged_union_t u;

  initial begin
    // Error: tagged expression can only be used with tagged union type
    u = tagged a 42;
  end
endmodule
