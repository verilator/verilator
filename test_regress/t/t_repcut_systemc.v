// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input reset,
    input [6:0] x7,
    input [14:0] x15 /*verilator sc_biguint*/,
    input [32:0] x33 /*verilator sc_biguint*/,
    input [64:0] x65 /*verilator sc_bv*/,
    output logic [6:0] q7,
    output logic [14:0] q15 /*verilator sc_biguint*/,
    output logic [32:0] q33 /*verilator sc_biguint*/,
    output logic [64:0] q65 /*verilator sc_bv*/
);
  always @(posedge clk) begin
    q7 <= reset ? '0 : q7 + x7;
    q15 <= reset ? '0 : q15 ^ x15;
    q33 <= reset ? '0 : q33 + x33;
    q65 <= reset ? '0 : {q65[63:0], q65[64]} ^ x65;
  end
endmodule
