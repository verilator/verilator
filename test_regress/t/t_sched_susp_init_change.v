// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Vaibhav Binwal
// SPDX-License-Identifier: CC0-1.0

// A change made by an 'initial' block at time 0 triggers an 'always' the same
// way whether or not the 'always' can suspend (#9066)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub (
    input logic clk,
    output int cnt_n,
    output int cnt_s
);
  bit never;
  initial cnt_n = 0;
  initial cnt_s = 0;
  always @(clk) cnt_n++;  // Non-suspendable
  always @(clk) begin  // Suspendable
    cnt_s++;
    if (never) #1;
  end
endmodule

module t;
  bit never;

  // Change sensitivity, 'initial' before the 'always' blocks in source order
  logic chg = 0;
  initial chg = 1;
  int cnt_chg_n = 0;
  int cnt_chg_s = 0;
  always @(chg) cnt_chg_n++;
  always @(chg) begin
    cnt_chg_s++;
    if (never) #1;
  end

  // Edge sensitivities, 'initial' after the 'always' blocks in source order
  logic pos = 0;
  logic neg = 1;
  int cnt_pos_n = 0;
  int cnt_pos_s = 0;
  int cnt_neg_n = 0;
  int cnt_neg_s = 0;
  always @(posedge pos) cnt_pos_n++;
  always @(posedge pos) begin
    cnt_pos_s++;
    if (never) #1;
  end
  always @(negedge neg) cnt_neg_n++;
  always @(negedge neg) begin
    cnt_neg_s++;
    if (never) #1;
  end
  initial begin
    pos = 1;
    neg = 0;
  end

  // No change at time 0, so no process fires
  logic same = 0;
  initial same = 0;
  int cnt_same_n = 0;
  int cnt_same_s = 0;
  always @(same) cnt_same_n++;
  always @(same) begin
    cnt_same_s++;
    if (never) #1;
  end

  // The 'always' blocks are in a different scope than the 'initial'
  logic sub_clk = 0;
  int cnt_sub_n;
  int cnt_sub_s;
  sub u_sub (
      .clk(sub_clk),
      .cnt_n(cnt_sub_n),
      .cnt_s(cnt_sub_s)
  );
  initial sub_clk = 1;

  initial begin
    #1;
    `checkd(cnt_chg_n, 1);
    `checkd(cnt_chg_s, 1);
    `checkd(cnt_pos_n, 1);
    `checkd(cnt_pos_s, 1);
    `checkd(cnt_neg_n, 1);
    `checkd(cnt_neg_s, 1);
    `checkd(cnt_same_n, 0);
    `checkd(cnt_same_s, 0);
    `checkd(cnt_sub_n, 1);
    `checkd(cnt_sub_s, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
