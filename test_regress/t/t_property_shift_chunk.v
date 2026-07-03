// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A ##130 delay is a 129-vertex shift chain packed across three <=64-bit
// vectors (verilator/verilator#7792 optimization). This exercises the
// cross-chunk carry: each next vector's bit 0 injects the previous vector's top
// bit through the shared clocked predecessor. res is high only exactly 130
// cycles after the single antecedent match, so an off-by-one or dropped carry
// makes the consequent miss and the assert fire.

module t (
    input clk
);
  int cyc = 0;
  wire trig = (cyc == 5);
  wire res = (cyc == 5 + 130);

  int n_fire = 0;

  assert property (@(posedge clk) trig |-> ##130 res)
  else n_fire <= n_fire + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 160) begin
      `checkd(n_fire, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
