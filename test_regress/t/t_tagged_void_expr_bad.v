// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when void member is given an expression

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  VInt v;

  initial begin
    v = tagged Invalid (42);  // Error: void member shouldn't have value
  end
endmodule
