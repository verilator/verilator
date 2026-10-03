// DESCRIPTION: Verilator: Subgraph fallback points to zero-delay RTL
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk;
  wire q;

  sg_fallback_delay_line i0 (.clk(clk), .q(q));

  initial begin
    #0;
  end
endmodule

module sg_fallback_delay_line (
  input logic clk,
  output logic q = 0
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= ~q;
endmodule
