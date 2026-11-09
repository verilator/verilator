// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A nonblocking event trigger of an event in a struct, which is not split into its members
typedef struct {
  event e;
  int x;
} s_t;

module t (
    input clk
);
  s_t s  /*verilator public_flat_rw*/;
  always @(posedge clk) ->>s.e;
endmodule
