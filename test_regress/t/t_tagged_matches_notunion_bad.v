// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when matches expression is not a tagged union type
// This tests V3Tagged.cpp:308 error message specifically

module t;
  // Declare a tagged union to trigger V3Tagged pass
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  VInt v;
  int x;

  initial begin
    v = tagged Invalid;
    // Error: x is int, not a tagged union
    if (x matches tagged Valid .val) begin
      $display("val = %d", val);
    end
  end
endmodule
