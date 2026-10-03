// DESCRIPTION: Verilator: Shared subgraph logic preserves per-instance initial values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic clk,
  output wire [6:0] b
);
  sg_shared_initial i_a (.clk(clk), .d(7'd3), .q());
  sg_shared_initial i_b (.clk(clk), .d(7'd5), .q(b));
endmodule

module sg_shared_initial (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 1
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
endmodule
