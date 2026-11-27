// DESCRIPTION: Verilator: Native decoder cache lifetime regression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input reset,
    input en_a,
    input en_b,
    input [6:0] a,
    input [6:0] b,
    input [127:0] mask,
    output reg [127:0] qa,
    output reg [127:0] qb,
    output reg [127:0] qc
);
  wire [127:0] da;
  wire [127:0] db;
  // Independent varying masks retain comparison fanout instead of collapsing
  // an entire one-hot vector into a single shift.
  for (genvar i = 0; i < 128; ++i) begin
    assign da[i] = (a == 7'(i)) ^ mask[i];
    assign db[i] = (b != 7'(i)) ^ mask[127-i];
  end
  always @(posedge clk) begin
    if (reset) begin
      qa <= '0;
      qb <= '0;
      qc <= '0;
    end else begin
      if (en_a) qa <= da;
      if (en_b) qb <= db;
      if (en_a && en_b) qc <= da ^ db;
    end
  end
endmodule
