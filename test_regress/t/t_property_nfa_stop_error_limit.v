// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Ignored worker-queued $stop against same-slot assertion evaluation.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  int passes = 0;

  assert property (@(posedge clk) 1'b1 ##1 1'b1) passes++;

  default clocking cb @(posedge clk);
  endclocking

  always @(posedge clk) begin
    cyc <= cyc + 1;
    // A clocked process is emitted inside an eval mtask in threaded models
    if (cyc == 5) $stop;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always @(negedge clk) begin
    if (cyc == 10) `checkd(passes, 9);
  end

  final begin
    $stop;
    `checkd($past(cyc), 10);
  end

endmodule
