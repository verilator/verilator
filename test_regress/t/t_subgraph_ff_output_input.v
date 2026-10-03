// DESCRIPTION: Verilator: FF and input dependent output remains on the fallback path
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
  logic [6:0] d = 0;
  wire [6:0] y;

  sg_ff_output_input i0 (.clk(clk), .d(d), .y(y));

  initial begin
    #1 `checkh(y, 7'd3);
    d = 7'd5;
    #1 `checkh(y, 7'd6);
    clk = 1;
    #1 `checkh(y, 7'd1);
    d = 7'd2;
    #1 `checkh(y, 7'd6);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_ff_output_input (
  input logic clk,
  input logic [6:0] d,
  output wire [6:0] y
);
  /*verilator subgraph_boundary*/
  logic [6:0] q = 3;
  always_ff @(posedge clk) q <= q + 7'd1;
  assign y = q ^ d;
endmodule
