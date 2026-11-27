// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk_a,
    input logic clk_b,
    input logic [6:0] value,
    output logic [6:0] a = 7'h13,
    output logic [6:0] b = 7'h29,
    output logic [6:0] combined
);
  always @(posedge clk_a) a <= a + value;
  always @(posedge clk_b) b <= b ^ value;
  assign combined = a ^ b;
endmodule
