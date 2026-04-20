// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a, b;

  // Unsupported: multi-cycle sequence expression inside consecutive repetition
  assert property (@(posedge clk) (a ##1 b) [* 2] |-> a);

endmodule
