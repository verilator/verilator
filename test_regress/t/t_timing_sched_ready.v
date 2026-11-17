// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 0;
  always #1 clk = ~clk;

  // Several processes awaiting the same event share one trigger scheduler
  int cnt1 = 0;
  int cnt2 = 0;
  time time3 = 0;
  initial forever begin
    @(posedge clk);
    ++cnt1;
  end
  initial forever begin
    @(posedge clk);
    @(posedge clk);
    ++cnt2;
  end
  initial begin
    repeat (5) @(posedge clk);
    time3 = $time;
  end

  // Awaiting the opposite edge must not consume a pending static process trigger.
  bit rising_clk = 0;
  int rising_count = 0;
  always @(posedge rising_clk) ++rising_count;
  initial begin
    #1 rising_clk = 1;
    @(negedge rising_clk);
  end

  bit falling_clk = 1;
  int falling_count = 0;
  always @(negedge falling_clk) ++falling_count;
  initial begin
    #1 falling_clk = 0;
    @(posedge falling_clk);
  end

  initial begin
    #40;
    `checkd(cnt1, 20);
    `checkd(cnt2, 10);
    `checkd(time3, 9);
    `checkd(rising_count, 1);
    `checkd(falling_count, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
