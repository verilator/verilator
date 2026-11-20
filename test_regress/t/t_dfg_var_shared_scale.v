// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t #(
    parameter int N = 1
) (
    input [7:0] a,
    input [7:0] b,
    input [30:0] chain_a,
    input [30:0] chain_g,
    output [N*8-1:0] q,
    output [29:0] deadq,
    output [N*30-1:0] liveq
);
  wire [7:0] s = a & b;
  for (genvar i = 0; i < N; ++i) begin : copies
    wire [7:0] d = s;
    assign q[i*8+:8] = d & 8'h0f;
  end

  wire [29:0] live_a = chain_a[30:1] ^ 30'(s & 8'h0f);
  wire [29:0] chain_s = chain_a[30:1] & chain_g[30:1];
  wire [29:0] opposite = ~chain_s;
  wire [29:0] zero = chain_s & opposite;
  for (genvar i = 0; i < N; ++i) begin : chain
    wire [30:0] v;
    if (i == 0) begin
      assign v[30:1] = 30'(chain_a ^ chain_g);
    end
    else begin
      assign v[30:1] = 30'(chain[i-1].v ^ chain_g);
    end
    assign liveq[i*30+:30] = (chain_g[30:1] + 30'(i + 1)) * live_a;
  end
  assign deadq = 30'(chain[N-1].v) & zero;
endmodule
