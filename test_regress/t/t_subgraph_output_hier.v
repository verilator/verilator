// DESCRIPTION: Verilator: Publish FF outputs from internal subgraph hierarchy
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0)
// verilog_format: on

`timescale 1ns/1ps

module t;
  logic clk = 0;
  logic [6:0] d0 = 0;
  logic [6:0] d1 = 0;
  wire [6:0] q0;
  wire [6:0] q1;
  wire [6:0] mix0;
  wire [6:0] mix1;
  wire [6:0] sum0;
  wire [6:0] sum1;
  logic [6:0] expected0 = 1;
  logic [6:0] expected1 = 1;
  logic [6:0] expected_other0 = 1;
  logic [6:0] expected_other1 = 1;

  sg_output_hier i0 (.clk(clk), .d(d0), .q(q0), .mix(mix0), .sum(sum0));
  sg_output_hier i1 (.clk(clk), .d(d1), .q(q1), .mix(mix1), .sum(sum1));

  initial begin
    #1;
    for (int cycle = 0; cycle < 20; cycle++) begin
      `checkh(q0, expected0);
      `checkh(q1, expected1);
      `checkh(mix0, expected0 ^ expected_other0);
      `checkh(mix1, expected1 ^ expected_other1);
      `checkh(sum0, 7'(expected0 + expected_other0));
      `checkh(sum1, 7'(expected1 + expected_other1));
      d0 = 7'(cycle * 3 + 2);
      d1 = 7'(cycle * 5 + 7);
      #1;
      `checkh(q0, expected0);
      `checkh(q1, expected1);
      `checkh(mix0, expected0 ^ expected_other0);
      `checkh(mix1, expected1 ^ expected_other1);
      clk = 1;
      #1;
      expected_other0 = expected0 + 7'd3;
      expected_other1 = expected1 + 7'd3;
      expected0 = d0;
      expected1 = d1;
      `checkh(q0, expected0);
      `checkh(q1, expected1);
      `checkh(mix0, expected0 ^ expected_other0);
      `checkh(mix1, expected1 ^ expected_other1);
      `checkh(sum0, 7'(expected0 + expected_other0));
      `checkh(sum1, 7'(expected1 + expected_other1));
      clk = 0;
      #1;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_output_hier (
  input logic clk,
  input logic [6:0] d,
  output wire [6:0] q,
  output wire [6:0] mix,
  output wire [6:0] sum
);
  /*verilator subgraph_boundary*/
  wire [6:0] a;
  wire [6:0] b;
  sg_output_hier_ff u_a (.clk(clk), .d(d), .q(a));
  sg_output_hier_ff u_b (.clk(clk), .d(a + 7'd3), .q(b));
  assign q = a;
  assign mix = a ^ b;
  sg_output_hier_comb u_sum (.a(a), .b(b), .sum(sum));
endmodule

module sg_output_hier_ff (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 1
);
  /*verilator no_inline_module*/
  always_ff @(posedge clk) q <= d;
endmodule

module sg_output_hier_comb (
  input logic [6:0] a /*verilator public_flat*/,
  input logic [6:0] b /*verilator public_flat*/,
  output wire [6:0] sum
);
  /*verilator no_inline_module*/
  assign sum = a + b;
endmodule
