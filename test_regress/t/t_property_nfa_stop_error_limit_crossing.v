// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// A worker-queued $stop at the error limit suppresses same-slot assertion actions.

module t (
    input clk
);

  int cyc = 0;

  // The exact golden excludes ACTION_RAN for the stopping edge.
  assert property (@(posedge clk) 1'b1 ##1 1'b1) begin
    if ($sampled(cyc) == 5) $write("ACTION_RAN\n");
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    // A clocked process is emitted inside an eval mtask in threaded models.
    if (cyc == 5) $stop;
  end

endmodule
