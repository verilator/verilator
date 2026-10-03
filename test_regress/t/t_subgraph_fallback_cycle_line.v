// DESCRIPTION: Verilator: Subgraph fallback points into a combinational cycle
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic clk,
  output wire [7:0] y
);
  sg_fallback_cycle_line i0 (.clk(clk), .y(y));
endmodule

module sg_fallback_cycle_line (
  input logic clk,
  output wire [7:0] y
);
  /*verilator subgraph_boundary*/
  logic [7:0] q;
  logic [7:0] a;
  logic [7:0] b;

  assign a = b + 8'd1;
  assign b = a ^ q;
  always_ff @(posedge clk) q <= a;
  assign y = q;
endmodule
