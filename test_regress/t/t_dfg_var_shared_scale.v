// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t #(
    parameter int N = 1,
    parameter int NOBS = 2
) (
    input [7:0] a,
    input [7:0] b,
    output [7:0] real0,
    output [7:0] real1,
    output [N*8-1:0] q
);
  if (NOBS > 0) begin : obs0
    assign real0 = a & b;
  end
  if (NOBS > 1) begin : obs1
    assign real1 = a & b;
  end
  for (genvar i = 0; i < N; ++i) begin : copies
    wire [7:0] d = a & b;
    assign q[i*8+:8] = d & 8'h0f;
  end
endmodule
