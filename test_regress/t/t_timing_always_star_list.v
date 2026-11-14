// DESCRIPTION: Verilator: Verilog Test module
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
  // The implicit event list of an 'always @*' with timing controls (IEEE 1800-2023 9.4.2.2):
  // variables read only inside a called task, an event control or a wait condition are not in it

  // Timing control in a called task: each process runs once
  logic en = 1'b0;
  logic q_nba = 1'b0;
  logic q_dly = 1'b0;
  int runs = 0;
  task automatic toggle_nba();
    q_nba <= #5 ~q_nba;
  endtask
  task automatic toggle_dly();
    #5 q_dly = ~q_dly;
  endtask
  task automatic toggle_dly_outer();
    toggle_dly();
  endtask
  always @* if (en) toggle_nba();
  always @* begin
    ++runs;
    if (en) toggle_dly_outer();
  end

  int n_nba = 0;
  int n_dly = 0;
  always @(posedge q_nba) n_nba++;
  always @(posedge q_dly) n_dly++;

  // Event control and wait in the statement: woken by 'go' only, so each counts once
  logic tick = 1'b0;
  initial forever #3 tick = ~tick;
  logic go = 1'b0;
  logic ready = 1'b0;
  int n_ev = 0;
  int n_wait = 0;
  always @* begin
    @(posedge tick);
    if (go) n_ev++;
  end
  always @* begin
    wait (ready);
    if (go) n_wait++;
  end

  initial begin
    #10 en = 1'b1;
    go = 1'b1;
    #10 ready = 1'b1;
    #90;
    `checkd(n_nba, 1);
    `checkd(n_dly, 1);
    `checkd(runs, 1);
    `checkd(n_ev, 1);
    `checkd(n_wait, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
