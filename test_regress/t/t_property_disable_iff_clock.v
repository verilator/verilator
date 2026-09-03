// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// disable iff before the clocking event, same as the clock-first form (IEEE 1800-2023 A.2.10)
module t;
  logic clk = 0;
  always #5 clk = ~clk;  // Posedges at 5, 15, 25, ...
  logic a = 0;
  logic d = 0;
  int fails_canon = 0;
  int fails_reord = 0;
  int fails_weak = 0;

  ap_canon: assert property (@(posedge clk) disable iff (d) a |-> !a)
      else fails_canon = fails_canon + 1;
  ap_reord: assert property (disable iff (d) @(posedge clk) a |-> !a)
      else fails_reord = fails_reord + 1;
  ap_weak: assert property (disable iff (d) @(posedge clk) weak(!a))
      else fails_weak = fails_weak + 1;
  cp_strong: cover property (disable iff (d) @(posedge clk) strong(a));

  initial begin
    #5 a = 1;   // Fails at posedge 15
    #10 a = 0;
    #5 d = 1;
    #5 a = 1;   // Disabled at posedge 35
    #10 a = 0;
    #5 d = 0;
    #5 a = 1;   // Fails at posedge 55
    #10 a = 0;
    #10 $finish;
  end

  final begin
    `checkd(fails_canon, fails_reord);
    `checkd(fails_canon, 2);
    `checkd(fails_weak, 2);
    $write("*-* All Finished *-*\n");
  end
endmodule
