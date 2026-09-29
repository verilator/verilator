// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [7:0] i,
    output logic [31:0] oa,
    output logic [31:0] ob
);
  logic [31:0] a[6];
  logic [31:0] b[6];
  for (genvar k = 0; k < 6; ++k) begin : g
    always_ff @(posedge clk) a[k] <= (a[k] + {24'd0, i}) ^ 32'(k + 1);
    always_ff @(posedge clk) b[k] <= (b[k] - {24'd0, i}) ^ 32'(k + 7);
  end
  assign oa = a[0] ^ a[1] ^ a[2] ^ a[3] ^ a[4] ^ a[5];
  assign ob = b[0] + b[1] + b[2] + b[3] + b[4] + b[5];
endmodule
