// DESCRIPTION: Verilator: Separate combinational procedures write one array
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module t;
  logic clk = 0;
  logic [7:0] d = 0;
  logic [7:0] expected = 1;
  wire [7:0] y;
  wire [7:0] z;

  sg_multi_writer child (.clk(clk), .d(d), .y(y), .z(z));

  initial begin
    #1;
    for (int cycle = 0; cycle < 6; cycle++) begin
      if (y !== expected) $stop;
      if (z !== ((expected ^ 8'h5a) ^ (expected + 8'd3))) $stop;
      d = 8'(cycle + 1);
      #1;
      if (y !== expected) $stop;
      if (z !== ((expected ^ 8'h5a) ^ (expected + 8'd3))) $stop;
      clk = 1;
      #1;
      expected = expected + d;
      if (y !== expected) $stop;
      if (z !== ((expected ^ 8'h5a) ^ (expected + 8'd3))) $stop;
      clk = 0;
      #1;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_multi_writer (
  input logic clk,
  input logic [7:0] d,
  output logic [7:0] y = 1,
  output wire [7:0] z
);
  /*verilator subgraph_boundary*/
  logic [7:0] parts [2];

  function automatic logic [7:0] mix0(input logic [7:0] x);
    // verilator no_inline_task
    return x ^ 8'h5a;
  endfunction

  function automatic logic [7:0] mix1(input logic [7:0] x);
    // verilator no_inline_task
    return x + 8'd3;
  endfunction

  /* verilator lint_off MULTIDRIVEN */
  always_comb parts[0] = mix0(y);
  always_comb parts[1] = mix1(y);
  /* verilator lint_on MULTIDRIVEN */
  assign z = parts[0] ^ parts[1];
  always_ff @(posedge clk) y <= y + d;
endmodule
