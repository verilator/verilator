// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged expression in non-assignment context (should error)
// Covers V3Tagged.cpp line 639 (E_UNSUPPORTED error path)

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  initial begin
    // Tagged expression used in $display context, not assignment RHS
    $display("%d", tagged Valid (42));
  end
endmodule
