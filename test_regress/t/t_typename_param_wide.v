// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub #(
    parameter int W = 1,
    parameter logic [W-1:0] P = '0
);
  // Named with the value of P
  typedef struct packed {logic a;} t;
endmodule

module t #(
    parameter int W = 1
);
  sub #(
      .W(W),
      .P('1)
  ) u ();
endmodule
