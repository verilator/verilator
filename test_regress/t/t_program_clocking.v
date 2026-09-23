// DESCRIPTION: Verilator: Program clocking event scheduling test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

program t;
  bit woke_at_first_event = 0;
  bit woke_at_dynamic_event = 0;
  bit checked_clocking_output = 0;
  bit checked_skewed_outputs = 0;

  initial begin
    #1;
    `checkd(int'($time), 1)
    @(tb_top.mck);
    `checkd(int'($time), 3)
    #3;
    `checkd(woke_at_first_event, 1)
    `checkd(woke_at_dynamic_event, 1)
    `checkd(checked_clocking_output, 1)
    `checkd(checked_skewed_outputs, 1)
    $write("*-* All Finished *-*\n");
    $finish;
  end

  // Drives mature in Re-NBA after coincident program code (IEEE 1800-2023 14.16)
  initial begin
    @(tb_top.sck);
    tb_top.sck.zero_out <= 7'd11;
    tb_top.sck.skew_out <= 7'd13;
    #1;
    `checkd(tb_top.zero_out, 11)
    `checkd(tb_top.zero_time, 1)
    tb_top.sck.zero_out <= 7'd21;
    tb_top.sck.skew_out <= 7'd23;
    @(tb_top.sck);
    `checkd(int'($time), 3)
    tb_top.sck.zero_out <= 7'd31;
    tb_top.sck.skew_out <= 7'd33;
    #2;
    `checkd(tb_top.zero_out, 31)
    `checkd(tb_top.skew_out, 33)
    `checkd(tb_top.zero_changes, 2)
    `checkd(tb_top.skew_changes, 2)
    `checkd(tb_top.zero_time, 3)
    `checkd(tb_top.skew_time, 4)
    checked_skewed_outputs = 1;
  end

  initial begin
    @(tb_top.mck);
    `checkd(int'($time), 1)
    woke_at_first_event = 1;
  end

  initial begin
    fork
      #1 woke_at_dynamic_event = 1;
    join_none
    wait fork;
    `checkd(int'($time), 1)
    `checkd(woke_at_dynamic_event, 1)
  end

  initial begin
    @(tb_top.mck);
    tb_top.mck.driven <= 1;
    @(tb_top.mck);
    `checkd(int'($time), 3)
    `checkd(tb_top.driven, 1)
    checked_clocking_output = 1;
  end
endprogram

module tb_top;
  bit clk = 0;
  bit driven = 0;
  bit [6:0] zero_out;
  bit [6:0] skew_out;
  int zero_changes;
  int skew_changes;
  int zero_time;
  int skew_time;
  t test ();
  always #1 clk = ~clk;
  clocking mck @(posedge clk);
    output #0 driven;
  endclocking
  clocking sck @(posedge clk);
    output #0 zero_out;
    output #1 skew_out;
  endclocking
  always @(zero_out) begin
    if ($time != 0) begin
      ++zero_changes;
      zero_time = int'($time);
    end
  end
  always @(skew_out) begin
    if ($time != 0) begin
      ++skew_changes;
      skew_time = int'($time);
    end
  end
endmodule
