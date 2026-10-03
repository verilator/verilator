// DESCRIPTION: Verilator: Fallback of a subgraph with independent clocks preserves both events
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
  logic clk_a = 0;
  logic clk_b = 0;
  wire [6:0] a;
  wire [6:0] b;

  sg_fallback_multiclock i0 (.clk_a(clk_a), .clk_b(clk_b), .a(a), .b(b));

  initial begin
    #1 clk_b = 1;
    #1 `checkh(a, 7'd0);
    `checkh(b, 7'd1);
    clk_b = 0;
    #1 clk_a = 1;
    #1 `checkh(a, 7'd1);
    `checkh(b, 7'd1);
    clk_a = 0;
    #1 clk_b = 1;
    #1 `checkh(a, 7'd1);
    `checkh(b, 7'd2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_fallback_multiclock (
  input logic clk_a,
  input logic clk_b,
  output logic [6:0] a = 0,
  output logic [6:0] b = 0
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk_a) a <= a + 7'd1;
  always_ff @(posedge clk_b) b <= b + 7'd1;
endmodule
