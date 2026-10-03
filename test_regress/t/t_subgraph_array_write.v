// DESCRIPTION: Verilator: Subgraph output cone with selected array writes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module t;
  logic clk = 0;
  logic [7:0] d0 = 0;
  logic [7:0] d1 = 0;
  logic [7:0] expected0 = 1;
  logic [7:0] expected1 = 1;
  wire [7:0] y0;
  wire [7:0] y1;

  sg_array_write i0 (.clk(clk), .d(d0), .y(y0));
  sg_array_write i1 (.clk(clk), .d(d1), .y(y1));

  initial begin
    #1;
    for (int cycle = 0; cycle < 6; cycle++) begin
      if (y0 !== ((expected0 ^ 8'h5a) ^ (expected0 + 8'd3))) $stop;
      if (y1 !== ((expected1 ^ 8'h5a) ^ (expected1 + 8'd3))) $stop;
      d0 = 8'(cycle + 1);
      d1 = 8'(cycle * 2 + 3);
      #1;
      if (y0 !== ((expected0 ^ 8'h5a) ^ (expected0 + 8'd3))) $stop;
      if (y1 !== ((expected1 ^ 8'h5a) ^ (expected1 + 8'd3))) $stop;
      clk = 1;
      #1;
      expected0 = expected0 + d0;
      expected1 = expected1 + d1;
      if (y0 !== ((expected0 ^ 8'h5a) ^ (expected0 + 8'd3))) $stop;
      if (y1 !== ((expected1 ^ 8'h5a) ^ (expected1 + 8'd3))) $stop;
      clk = 0;
      #1;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_array_write (
  input logic clk,
  input logic [7:0] d,
  output wire [7:0] y
);
  /*verilator subgraph_boundary*/
  logic [7:0] q = 1;
  logic [7:0] bits [2];

  function automatic logic [7:0] mix(input logic [7:0] x);
    return x ^ 8'h5a;
  endfunction

  always_comb begin
    bits[0] = mix(q);
    bits[1] = q + 8'd3;
  end
  assign y = bits[0] ^ bits[1];
  always_ff @(posedge clk) q <= q + d;
endmodule
