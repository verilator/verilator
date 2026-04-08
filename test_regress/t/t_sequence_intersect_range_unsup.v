// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a, b, c, d;

  // Range delay in intersect operand is unsupported
  assert property (@(posedge clk)
      (a ##[1:5] b) intersect (c ##2 d));

endmodule
