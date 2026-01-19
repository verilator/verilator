// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when tagged expression used without context type

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  initial begin
    // Error: tagged expression requires a context type
    $display(tagged Valid 42);
  end
endmodule
