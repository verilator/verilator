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

  // Sequence without arguments
  sequence seq_ab;
    a && b;
  endsequence

  // Sequence with formal arguments (default input direction)
  sequence seq_check(logic sig1, logic sig2);
    sig1 && sig2;
  endsequence

  // Overlapping implication with sequence ref (no args)
  assert property (@(posedge clk) seq_ab |-> c);

  // Non-overlapping implication
  assert property (@(posedge clk) seq_ab |=> c);

  // Sequence with args, multiple references with different actuals
  assert property (@(posedge clk) seq_check(a, b) |-> c);
  assert property (@(posedge clk) seq_check(b, c) |-> a);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      2, 5: begin
        a <= 1'b1;
        b <= 1'b1;
        c <= 1'b1;
      end
      3, 6: begin
        a <= 1'b0;
        b <= 1'b0;
        c <= 1'b1;
      end  // c stays high for |=> check
      default: begin
        a <= 1'b0;
        b <= 1'b0;
        c <= 1'b0;
      end
    endcase
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
