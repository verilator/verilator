// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Ignored worker-queued $stop against same-slot assertion evaluation.

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
    if (cyc == 10) $display("passes=%0d", passes);
  end

  final begin
    $stop;
    $display("final_past_cyc=%0d", $past(cyc));
  end

endmodule
