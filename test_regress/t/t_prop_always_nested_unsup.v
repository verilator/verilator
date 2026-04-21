// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a;
  logic b;

  // Property operators nested inside bounded always: all rejected with one
  // unified message (IEEE 1800-2023 16.12.11).
  assert property (@(posedge clk) always [0:3] (a |-> b));
  assert property (@(posedge clk) always [0:3] (a |=> b));

  // Sequence operator nested inside bounded always: same rejection path.
  assert property (@(posedge clk) always [0:3] (a ##1 b));

endmodule
