// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// An ignored worker-queued $stop must not suppress same-slot assertion evaluation.

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $fatal; end while(0);
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
    // This clocked process ensures threaded models queue the stop from an eval mtask.
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
    `checkd($past(cyc), 9);
  end

endmodule
