// DESCRIPTION: Verilator: Shared subgraph publishes an FF-derived conditional output
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
  logic [6:0] expected0 = 1;
  logic [6:0] expected1 = 1;
  wire [6:0] y0;
  wire [6:0] y1;

  sg_comb_branch_out i0 (.clk(clk), .d(d0), .y(y0));
  sg_comb_branch_out i1 (.clk(clk), .d(d1), .y(y1));

  initial begin
    #1;
    for (int cycle = 0; cycle < 8; cycle++) begin
      `checkh(y0, ~(expected0[0] ? expected0 ^ 7'h35 : expected0 + 7'd7));
      `checkh(y1, ~(expected1[0] ? expected1 ^ 7'h35 : expected1 + 7'd7));
      d0 = 7'(cycle + 1);
      d1 = 7'(cycle * 3 + 2);
      #1;
      `checkh(y0, ~(expected0[0] ? expected0 ^ 7'h35 : expected0 + 7'd7));
      `checkh(y1, ~(expected1[0] ? expected1 ^ 7'h35 : expected1 + 7'd7));
      clk = 1;
      #1;
      expected0 = expected0 + d0 + (expected0[0] ? 7'd1 : 7'd2);
      expected1 = expected1 + d1 + (expected1[0] ? 7'd1 : 7'd2);
      `checkh(y0, ~(expected0[0] ? expected0 ^ 7'h35 : expected0 + 7'd7));
      `checkh(y1, ~(expected1[0] ? expected1 ^ 7'h35 : expected1 + 7'd7));
      clk = 0;
      #1;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module sg_comb_branch_out (
  input logic clk,
  input logic [6:0] d,
  output wire [6:0] y
);
  /*verilator subgraph_boundary*/
  logic [6:0] q = 1;
  logic [6:0] mix /*verilator public_flat*/;
  logic [6:0] next_q /*verilator public_flat*/;
  function automatic logic [6:0] advance(input logic [6:0] value,
                                        input logic [6:0] delta,
                                        input logic [6:0] offset);
    // verilator no_inline_task
    return value + delta + offset;
  endfunction
  always_comb begin
    if (q[0]) begin
      mix = q ^ 7'h35;
      next_q = advance(q, d, 7'd1);
    end else begin
      mix = q + 7'd7;
      next_q = advance(q, d, 7'd2);
    end
  end
  assign y = ~mix;
  always_ff @(posedge clk) q <= next_q;
endmodule
