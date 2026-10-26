// DESCRIPTION: Verilator: Clocking block with a clocking event of several edges
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`timescale 1ns / 1ps
module t;
  logic clk = 0;
  always #5 clk = ~clk;

  clocking cb_both @(posedge clk or negedge clk);
  endclocking

  clocking cb_edge @(edge clk);
  endclocking

  clocking cb_pos @(posedge clk);
  endclocking

  // Default clocking, for cycle delays
  default clocking cb_dflt @(posedge clk or negedge clk);
  endclocking

  logic [6:0] cnt = 0;
  always @(posedge clk or negedge clk) cnt <= cnt + 7'd1;

  logic [6:0] drv = 0;
  clocking cb_drv @(posedge clk or negedge clk);
    input #1step cnt;
    output drv;
  endclocking

  int n_both, n_edge, n_plain, n_pos;
  time t_dly1, t_dly2;

  initial
    forever begin
      @(cb_both);
      n_both++;
    end

  initial
    forever begin
      @(cb_edge);
      n_edge++;
    end

  initial
    forever begin
      @(cb_pos);
      n_pos++;
    end

  initial
    forever begin
      @(posedge clk or negedge clk);
      n_plain++;
    end

  // Cycle delays count every edge
  initial begin
    ##1;
    t_dly1 = $time;
    ##2;
    t_dly2 = $time;
  end

  // Sampled input is the value before the edge, synchronous drive waits for the next edge
  initial begin
    @(cb_drv);
    `checkd(cb_drv.cnt, 0);
    cb_drv.drv <= ##1 7'd5;
    `checkd(drv, 0);
    @(cb_drv);
    `checkd(cb_drv.cnt, 1);
    #1;
    `checkd(drv, 5);
  end

  initial begin
    #92;
    `checkd(n_plain, 18);
    `checkd(n_both, n_plain);
    `checkd(n_edge, n_plain);
    `checkd(n_pos, 9);
    `checkd(t_dly1, 5);
    `checkd(t_dly2, 15);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
