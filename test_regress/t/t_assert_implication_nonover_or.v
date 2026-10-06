// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Brambilla
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a = 0, x = 0, y = 0;
  int fail_or = 0, fail_delay_or = 0, fail_single = 0, fail_and = 0;

  // a in cycle 3; x and y stay low, so every property below must fail exactly once (cycle 4)
  assert property (@(posedge clk) a |=> (x || y))
  else fail_or = fail_or + 1;
  assert property (@(posedge clk) a |-> ##1 (x || y))
  else fail_delay_or = fail_delay_or + 1;
  assert property (@(posedge clk) a |=> x)
  else fail_single = fail_single + 1;
  assert property (@(posedge clk) a |=> (x && y))
  else fail_and = fail_and + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= (cyc == 2);
    if (cyc == 10) begin
      `checkd(fail_or, 1);
      `checkd(fail_delay_or, 1);
      `checkd(fail_single, 1);
      `checkd(fail_and, 1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
