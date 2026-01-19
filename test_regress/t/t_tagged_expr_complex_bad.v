// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error for unpacked tagged union in non-simple assignment context

module t;
  // Unpacked tagged union (string member forces unpacked storage)
  typedef union tagged {
    void Invalid;
    string StrVal;
  } VString;

  VString v;

  // Error: continuous assignment is not a simple assignment context for unpacked union
  assign v = tagged StrVal ("hello");
endmodule
