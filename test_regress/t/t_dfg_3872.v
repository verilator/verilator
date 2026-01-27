// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module top(
  input  wire [1:0] i,
  output wire [3:0] o
);
  assign o = 4'd2 ** i;
endmodule
