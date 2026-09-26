// DESCRIPTION: Verilator: Nonblocking event triggers in suspendable processes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  bit clk;
  event e_init;
  event e_dly;
  event e_clk;
  int init_time = -1;
  int dly_time = -1;
  int clk_times;

  always #5 clk = ~clk;

  initial begin
    @e_init;
    init_time = int'($time);
  end
  initial begin
    @e_dly;
    dly_time = int'($time);
  end
  always @e_clk ++clk_times;

  // The event is triggered in the NBA region (IEEE 1800-2023 15.5.1)
  initial ->>e_init;

  initial begin
    #1 ->>e_dly;
    `checkd(e_dly.triggered, 0)
    #0 `checkd(e_dly.triggered, 0)
  end

  always begin
    @(posedge clk);
    ->>e_clk;
  end

  initial begin
    #22;
    `checkd(init_time, 0)
    `checkd(dly_time, 1)
    `checkd(clk_times, 2)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
