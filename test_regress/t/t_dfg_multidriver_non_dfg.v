// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Geza Lore
// SPDX-License-Identifier: CC0-1.0

`default_nettype none

module t (
    input wire i,
    output wire o
);
  logic a;
  logic b;
  assign a = ~i;
  assign b = a;
  assign o = b;
endmodule
