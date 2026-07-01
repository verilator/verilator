// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a, b, c, d, e;

  default clocking @(posedge clk);
  endclocking

  // Two ranged cycle delays in one intersect operand is unsupported
  assert property ((a ##[1:3] b ##[1:2] c) intersect (d ##2 e));

  // Single common length, but an operand is not a plain boolean sequence
  assert property ((a throughout (b ##1 c)) intersect (d ##[0:2] e));

  // Both operands vary over a range and carry internal structure
  assert property ((a ##[1:3] (b ##1 c)) intersect (d ##[2:4] e));

  // Operand top-level delay fixed but length varies via a nested range
  assert property ((a ##2 (b ##[1:3] c)) intersect (d ##[3:5] e));

endmodule
