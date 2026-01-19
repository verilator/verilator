// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when tagged union is used in constant expression context

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  // Function returning tagged union
  function VInt make_valid(int x);
    make_valid = tagged Valid x;
  endfunction

  // Error: Tagged expressions not supported in constant context
  localparam VInt CONST_VAL = make_valid(42);
endmodule
