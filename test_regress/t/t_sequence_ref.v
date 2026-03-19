// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;
  logic a, b, c;

  sequence seq_ab;
    a && b;
  endsequence

  // Overlapping implication with sequence ref
  assert property (@(posedge clk) seq_ab |-> c);

  // Non-overlapping implication
  assert property (@(posedge clk) seq_ab |=> c);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      2: begin a <= 1'b1; b <= 1'b1; c <= 1'b1; end
      3: begin a <= 1'b0; b <= 1'b0; c <= 1'b1; end
      default: begin a <= 1'b0; b <= 1'b0; c <= 1'b0; end
    endcase
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
