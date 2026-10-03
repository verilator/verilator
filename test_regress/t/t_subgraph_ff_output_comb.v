// DESCRIPTION: Verilator: FF-derived combinational outputs of shared subgraphs
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
  logic [6:0] drive = 0;
  wire [6:0] y0;
  wire [6:0] y1;
  wire [6:0] z0;
  wire [6:0] z1;
  wire [6:0] parent_y = y0 + y1;
  logic [6:0] expected_a0 = 1;
  logic [6:0] expected_b0 = 3;
  logic [6:0] expected_a1 = 1;
  logic [6:0] expected_b1 = 3;
  logic [6:0] next_a0;
  logic [6:0] next_a1;

  sg_ff_output_comb i0 (.clk(clk), .d(d0), .y(y0), .z(z0));
  sg_ff_output_comb i1 (.clk(clk), .d(d1 ^ drive), .y(y1), .z(z1));

  always_ff @(posedge clk) drive <= drive + 7'd1;

  initial begin
    #1;
    `checkh(y0, ~(expected_a0 ^ expected_b0));
    `checkh(y1, ~(expected_a1 ^ expected_b1));
    `checkh(z0, expected_a0 + expected_b0);
    `checkh(z1, expected_a1 + expected_b1);
    for (int cycle = 0; cycle < 8; cycle++) begin
      d0 = 7'(cycle + 2);
      d1 = 7'(cycle * 3 + 1);
      next_a0 = (expected_a0 ^ expected_b0) + d0;
      next_a1 = (expected_a1 ^ expected_b1) + (d1 ^ drive);
      #1;
      `checkh(y0, ~(expected_a0 ^ expected_b0));
      `checkh(y1, ~(expected_a1 ^ expected_b1));
      clk = 1;
      #1;
      expected_a0 = next_a0;
      expected_a1 = next_a1;
      expected_b0 = expected_b0 + 7'd3;
      expected_b1 = expected_b1 + 7'd3;
      `checkh(y0, ~(expected_a0 ^ expected_b0));
      `checkh(y1, ~(expected_a1 ^ expected_b1));
      `checkh(z0, expected_a0 + expected_b0);
      `checkh(z1, expected_a1 + expected_b1);
      `checkh(parent_y, 7'(~(expected_a0 ^ expected_b0) +
                            ~(expected_a1 ^ expected_b1)));
      clk = 0;
      #1;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_ff_output_comb (
  input logic clk,
  input logic [6:0] d,
  output wire [6:0] y,
  output wire [6:0] z
);
  /*verilator subgraph_boundary*/
  logic [6:0] a = 1;
  logic [6:0] b = 3;
  wire [6:0] mix = a ^ b;
  assign y = ~mix;
  assign z = a + b;
  always_ff @(posedge clk) begin
    a <= mix + d;
    b <= b + 7'd3;
  end
endmodule
