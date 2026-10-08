// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) \
  do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0)
// verilog_format: on

module t;
  int a;
  int active;  // Copies of the always block currently running
  int max_active;
  int runs;

  class waiter;
    task wait5();
      ++active;
      if (active > max_active) max_active = active;
      #5;
      --active;
      ++runs;
    endtask
  endclass

  waiter w = new;

  // Timing control is only in a called (not inlined) task
  always @* if (a >= 0) w.wait5();

  initial begin
    #1 a = 1;
    #2 a = 2;  // Changes while the always is still waiting
    #20;
    `checkd(max_active, 1);
    if (runs == 0) `stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
