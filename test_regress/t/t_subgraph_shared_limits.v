// DESCRIPTION: Verilator: Shared subgraph logic respects clock domains and hierarchy
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic clk_a,
  input logic clk_b,
  input logic [6:0] d,
  output logic [6:0] q0,
  output logic [6:0] q1,
  output logic [6:0] q2,
  output logic [6:0] q3,
  output logic [6:0] q4,
  output logic [6:0] q5,
  output logic [6:0] q6,
  output logic [6:0] q7,
  output logic [6:0] q8,
  output logic [6:0] q9,
  output logic [6:0] q10,
  output logic [6:0] tap9,
  output logic [6:0] tap10
);
  sg_shared_limit_count i0 (.clk(clk_a), .d(d), .q(q0));
  sg_shared_limit_count i1 (.clk(clk_a), .d(d), .q(q1));
  sg_shared_limit_count i2 (.clk(clk_a), .d(d), .q(q2));
  sg_shared_limit_clock i3 (.clk(clk_a), .d(d), .q(q3));
  sg_shared_limit_clock i4 (.clk(clk_b), .d(d), .q(q4));
  sg_shared_limit_wrapper i5 (.clk(clk_a), .d(d), .q0(q5), .q1(q6));
  sg_shared_limit_wrapper i6 (.clk(clk_a), .d(d), .q0(q7), .q1(q8));
  sg_shared_limit_comb i7 (.clk(clk_a), .d(d), .q(q9), .tap(tap9));
  sg_shared_limit_comb i8 (.clk(clk_a), .d(d), .q(q10), .tap(tap10));
endmodule

module sg_shared_limit_comb (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q,
  output logic [6:0] tap
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
  always_comb tap = q + d;
endmodule

module sg_shared_limit_count (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
endmodule

module sg_shared_limit_clock (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
endmodule

module sg_shared_limit_wrapper (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q0,
  output logic [6:0] q1
);
  sg_shared_limit_nested i0 (.clk(clk), .d(d), .q(q0));
  sg_shared_limit_nested i1 (.clk(clk), .d(d), .q(q1));
endmodule

module sg_shared_limit_nested (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
endmodule
