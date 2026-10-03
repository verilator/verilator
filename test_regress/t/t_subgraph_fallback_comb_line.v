// DESCRIPTION: Verilator: Subgraph fallback points to unsupported combinational RTL
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  output wire [7:0] y0,
  output wire [7:0] y1
);
  logic clk;
  logic [7:0] d;

  sg_fallback_comb_line i0 (.clk(clk), .d(d), .y(y0));
  sg_fallback_comb_line i1 (.clk(clk), .d(d), .y(y1));
endmodule

module sg_fallback_comb_line (
  input logic clk,
  input logic [7:0] d,
  output wire [7:0] y
);
  /*verilator subgraph_boundary*/
  logic [7:0] q;
  logic [7:0] next_q;

  always_comb begin
    next_q = q + d;
    if (d[0]) $display("next_q=%0h", next_q);
  end
  always_ff @(posedge clk) q <= next_q;
  assign y = q;
endmodule
