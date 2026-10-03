// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// The package must be kept while the unused nested struct type still refers to it

package pkg;
  typedef struct {
    int x;
    struct {bit a, b;} nested;
  } s_t;
endpackage

module t;
  pkg::s_t unused;
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
