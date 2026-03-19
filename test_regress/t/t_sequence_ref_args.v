// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test named sequence with formal arguments referenced in a property
// IEEE 1800-2023 16.7, 16.8

module t (
    input clk
);

  int cyc = 0;
  logic a, b, c;

  // Sequence with formal arguments (boolean body, no ##)
  sequence seq_check(logic sig1, logic sig2);
    sig1 && sig2;
  endsequence

  // Sequence referenced multiple times with different arguments
  assert property (@(posedge clk) seq_check(a, b) |-> c);
  assert property (@(posedge clk) seq_check(b, c) |-> a);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      2, 5: begin a <= 1'b1; b <= 1'b1; c <= 1'b1; end
      default: begin a <= 1'b0; b <= 1'b0; c <= 1'b0; end
    endcase
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
