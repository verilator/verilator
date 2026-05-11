// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a;
  logic b;

  // IEEE-legal but engine has no sim-end liveness.
  assert property (@(posedge clk) always [2:$] a);

  // Nested sequence/property operators inside bounded always.
  assert property (@(posedge clk) always [0:3] (a |-> b));
  assert property (@(posedge clk) always [0:3] (a |=> b));
  assert property (@(posedge clk) always [0:3] (a ##1 b));

endmodule
