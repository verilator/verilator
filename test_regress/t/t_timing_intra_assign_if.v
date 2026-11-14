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
  // If/else assigning the same variable, only one branch with an intra-assignment delay
  logic en = 1'b0;
  logic q_then = 1'b0;
  logic q_else = 1'b0;
  always @(en or q_then)
    if (en) q_then <= #5 ~q_then;
    else q_then <= 1'b0;
  always @(en or q_else)
    if (!en) q_else <= 1'b0;
    else q_else <= #5 ~q_else;
  // Both branches delayed, by different amounts
  logic go = 1'b0;
  logic sel = 1'b0;
  logic q_two = 1'b0;
  int n_two = 0;
  always @(go or sel or q_two)
    if (sel) q_two <= #3 ~q_two;
    else q_two <= #7 ~q_two;
  always @(posedge q_two) n_two++;
  initial #1 go = 1'b1;

  initial begin
    #10 en = 1'b1;
    #6;  // t=16, both rose at t=15
    `checkd(q_then, 1'b1);
    `checkd(q_else, 1'b1);
    #1 en = 1'b0;  // t=17, the branch without delay clears both now
    #1;
    `checkd(q_then, 1'b0);
    `checkd(q_else, 1'b0);
    #10;
    `checkd(q_then, 1'b0);
    `checkd(q_else, 1'b0);
    // t=28: q_two toggles every 7 from t=1 (posedges at 8, 22), then every 3 once sel is set
    `checkd(n_two, 2);
    sel = 1'b1;
    #30;
    `checkd(n_two, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  // Blocking assignments: intra-assignment delay and event control in one branch only
  logic en_b = 1'b0;
  logic b_dly = 1'b0;
  logic b_ev = 1'b0;
  logic clk = 1'b0;
  initial forever #5 clk = ~clk;  // posedges at 5, 15, 25
  always @(en_b)
    if (en_b) b_dly = #5 1'b1;
    else b_dly = 1'b0;
  always @(en_b)
    if (en_b) b_ev = @(posedge clk) 1'b1;
    else b_ev = 1'b0;
  initial begin
    #10 en_b = 1'b1;
    #6;  // t=16
    `checkd(b_dly, 1'b1);
    `checkd(b_ev, 1'b1);
    #4 en_b = 1'b0;  // t=20, the branch without a timing control clears both now
    #1;
    `checkd(b_dly, 1'b0);
    `checkd(b_ev, 1'b0);
  end
endmodule
