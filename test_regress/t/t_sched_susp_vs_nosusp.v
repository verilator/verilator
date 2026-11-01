// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Sensitivities trigger a process the same way whether or not the process can suspend

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit never;

  logic sense_chg = 0;
  int cnt_chg_n = 0;
  int cnt_chg_s = 0;
  always @(sense_chg) cnt_chg_n++;
  always @(sense_chg) begin
    cnt_chg_s++;
    if (never) #1;
  end
  initial begin
    #1;
    `checkd(cnt_chg_n, 0);
    `checkd(cnt_chg_s, 0);
    repeat (3) begin
      #1;
      sense_chg = ~sense_chg;
    end
    #1;
    `checkd(cnt_chg_n, 3);
    `checkd(cnt_chg_s, 3);
  end

  logic sense_pos = 0;
  int cnt_pos_n = 0;
  int cnt_pos_s = 0;
  always @(posedge sense_pos) cnt_pos_n++;
  always @(posedge sense_pos) begin
    cnt_pos_s++;
    if (never) #1;
  end
  initial begin
    #1;
    `checkd(cnt_pos_n, 0);
    `checkd(cnt_pos_s, 0);
    repeat (3) begin
      #1;
      sense_pos = ~sense_pos;
    end
    #1;
    `checkd(cnt_pos_n, 2);
    `checkd(cnt_pos_s, 2);
  end

  logic sense_neg = 0;
  int cnt_neg_n = 0;
  int cnt_neg_s = 0;
  always @(negedge sense_neg) cnt_neg_n++;
  always @(negedge sense_neg) begin
    cnt_neg_s++;
    if (never) #1;
  end
  initial begin
    #1;
    `checkd(cnt_neg_n, 0);
    `checkd(cnt_neg_s, 0);
    repeat (3) begin
      #1;
      sense_neg = ~sense_neg;
    end
    #1;
    `checkd(cnt_neg_n, 1);
    `checkd(cnt_neg_s, 1);
  end

  logic sense_edg = 0;
  int cnt_edg_n = 0;
  int cnt_edg_s = 0;
  always @(edge sense_edg) cnt_edg_n++;
  always @(edge sense_edg) begin
    cnt_edg_s++;
    if (never) #1;
  end
  initial begin
    #1;
    `checkd(cnt_edg_n, 0);
    `checkd(cnt_edg_s, 0);
    repeat (3) begin
      #1;
      sense_edg = ~sense_edg;
    end
    #1;
    `checkd(cnt_edg_n, 3);
    `checkd(cnt_edg_s, 3);
  end

  event sense_event;
  int cnt_event_n = 0;
  int cnt_event_s = 0;
  always @(sense_event) cnt_event_n++;
  always @(sense_event) begin
    cnt_event_s++;
    if (never) #1;
  end
  initial begin
    #1;
    `checkd(cnt_event_n, 0);
    `checkd(cnt_event_s, 0);
    repeat (3) begin
      #1;
      ->sense_event;
    end
    #1;
    `checkd(cnt_event_n, 3);
    `checkd(cnt_event_s, 3);
  end

  initial begin
    #20;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
