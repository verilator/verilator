// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when tagged pattern uses non-existent member in if-matches
// This tests V3Tagged.cpp:447 error message specifically

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  VInt v;

  initial begin
    v = tagged Invalid;
    // Error: BadMember does not exist in the union
    if (v matches tagged BadMember .x) begin
      $display("x = %d", x);
    end
  end
endmodule
