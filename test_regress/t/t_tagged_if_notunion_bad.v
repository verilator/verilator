// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when if matches is used with non-tagged union type

module t;
  // Declare a tagged union to trigger V3Tagged pass
  typedef union tagged {
    void Dummy;
  } TaggedType;

  // Regular (non-tagged) union
  union packed {
    int a;
    int b;
  } u;

  initial begin
    // verilator lint_off WIDTHEXPAND
    // Error: Matches expression must be a tagged union type
    if (u matches tagged a .v)
      $display("matched");
    // verilator lint_on WIDTHEXPAND
  end
endmodule
