// DESCRIPTION: Verilator: DPI-C function in a subgraph next-state calculation
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module t;
  logic clk = 0;
  logic [31:0] d = 0;
  logic [31:0] d1 = 0;
  logic [31:0] expected = 1;
  logic [31:0] expected1 = 1;
  wire [31:0] y;
  wire [31:0] y1;
  wire [31:0] z;
  wire [31:0] z1;

  sg_dpi child (.clk(clk), .d(d), .y(y), .z(z));
  sg_dpi child1 (.clk(clk), .d(d1), .y(y1), .z(z1));

  initial begin
    #1;
    for (int cycle = 0; cycle < 5; cycle++) begin
      if (y !== expected) $stop;
      if (y1 !== expected1) $stop;
      if (z !== (expected * 3 + 1)) $stop;
      if (z1 !== (expected1 * 3 + 1)) $stop;
      d = 32'(cycle + 1);
      d1 = 32'(cycle * 2 + 1);
      #1;
      if (y !== expected) $stop;
      if (y1 !== expected1) $stop;
      if (z !== (expected * 3 + 1)) $stop;
      if (z1 !== (expected1 * 3 + 1)) $stop;
      clk = 1;
      #1;
      expected = (expected + d) * 3 + 1;
      expected1 = (expected1 + d1) * 3 + 1;
      if (y !== expected) $stop;
      if (y1 !== expected1) $stop;
      if (z !== (expected * 3 + 1)) $stop;
      if (z1 !== (expected1 * 3 + 1)) $stop;
      clk = 0;
      #1;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_dpi (
  input logic clk,
  input logic [31:0] d,
  output wire [31:0] y,
  output wire [31:0] z
);
  /*verilator subgraph_boundary*/
  import "DPI-C" function int dpi_scale(input int value);
  logic [31:0] q = 1;
  logic [31:0] next_q;
  function automatic int wrapped_scale(input int value);
    // verilator no_inline_task
    return dpi_scale(value);
  endfunction
  always_comb next_q = wrapped_scale(q + d);
  always_ff @(posedge clk) q <= next_q;
  assign y = q;
  assign z = dpi_scale(q);
endmodule
