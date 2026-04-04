// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a, b;

  // Bad: trailing consecutive repetition range in sequence expression
  assert property (@(posedge clk) b ##1 a[+]);

endmodule
