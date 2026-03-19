// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;
  logic a, b1, b2;

  // Overlapped: a |-> ##1 b1
  assert property (@(posedge clk) a |-> ##1 b1);

  // Overlapped with longer delay: a |-> ##2 b1
  assert property (@(posedge clk) a |-> ##2 b2);

  // Non-overlapped: a |=> ##2 b2 (1 implicit + 2 explicit = 3 cycles total)
  assert property (@(posedge clk) a |=> ##2 b2);

  always @(posedge clk) begin
    cyc <= cyc + 1;

    // a pulses at cyc==3
    a  <= (cyc == 2);

    // b1 true at cyc==4 (1 cycle after a for |-> ##1)
    b1 <= (cyc == 3);

    // b2 true at cyc==5 and cyc==6
    // cyc==5 covers |-> ##2, cyc==6 covers |=> ##2 (1 implicit + 2 explicit)
    b2 <= (cyc == 4 || cyc == 5);

    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
