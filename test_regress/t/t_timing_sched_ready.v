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

  initial begin
    #40;
    `checkd(cnt1, 20);
    `checkd(cnt2, 10);
    `checkd(time3, 9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
