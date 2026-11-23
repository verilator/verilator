// DESCRIPTION: Verilator: Per-domain automatic RepCut publication
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t #(
  parameter CONDITIONAL = 0
) (
  input logic clk_a, clk_b, clk_c, reset, enable,
  input logic [31:0] data,
  input logic [63:0] write_mask,
  output wire [128*1023-1:0] balanced, skewed,
  output wire [94:0] memory_view,
  output logic [62:0] narrow, auxiliary
);
  always_ff @(posedge clk_b)
    if (reset) narrow <= '0;
    else if (enable) narrow <= narrow + 63'(data);
  always_ff @(posedge clk_b)
    if (reset) auxiliary <= '0;
    else if (enable) auxiliary <= narrow + 63'(data);
  for (genvar g = 0; g < 128; ++g) begin : bank
    logic [1022:0] wide_a, wide_c;
    always_ff @(posedge clk_a)
      if (reset) wide_a <= 1023'(g);
      else if (!CONDITIONAL || write_mask[g/2]) wide_a <= wide_a ^ 1023'({32{data + 32'(g)}});
    always_ff @(posedge clk_c)
      if (reset) wide_c <= 1023'(g);
      else if (enable) wide_c <= wide_c ^ 1023'({32{data - 32'(g)}});
    assign balanced[1023*g+:1023] = wide_a;
    assign skewed[1023*g+:1023] = wide_c;
  end
  if (CONDITIONAL) begin : memories
    logic [94:0] words [8];
    always_ff @(posedge clk_b) begin
      if (reset) begin
        for (int j = 0; j < 8; ++j) words[j] <= 95'(j);
      end else if (enable) begin
        words[data[2:0]] <= words[data[2:0]] ^ 95'({3{data}});
        // The later write must win even when both ports alias.
        if (data[3]) words[data[2:0]] <= 95'({3{data + 32'd1}});
      end
    end
    assign memory_view = words[data[2:0]];
  end else begin
    assign memory_view = '0;
  end
endmodule
