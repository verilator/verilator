// DESCRIPTION: Verilator: Subgraph keeps a conditional combinational value across input changes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module t;
  logic clk = 0;
  logic en = 0;
  logic [7:0] d = 0;
  wire [7:0] q;

  sg_comb_latch child (.clk(clk), .en(en), .d(d), .q(q));

  task automatic tick;
    clk = 1;
    #1;
    clk = 0;
    #1;
  endtask

  initial begin
    #1;
    en = 1;
    d = 3;
    #1;
    tick();
    if (q !== 3) $stop;
    en = 0;
    d = 7;
    #1;
    tick();
    if (q !== 6) $stop;
    en = 1;
    d = 2;
    #1;
    tick();
    if (q !== 8) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_comb_latch (
  input logic clk,
  input logic en,
  input logic [7:0] d,
  output logic [7:0] q = 0
);
  /*verilator subgraph_boundary*/
  logic [7:0] held;
  /* verilator lint_off LATCH */
  always_comb if (en) held = d;
  /* verilator lint_on LATCH */
  always_ff @(posedge clk) q <= q + held;
endmodule
