// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a;
  logic b;

  // Nested sequence/property operators inside bounded always.
  assert property (@(posedge clk) always [0:3] (a |-> b));
  assert property (@(posedge clk) always [0:3] (a |=> b));
  assert property (@(posedge clk) always [0:3] (a ##1 b));
  // s_eventually inside bounded always or s_always, also as a consequent and procedural
  assert property (@(posedge clk) always [0:2] s_eventually b);
  assert property (@(posedge clk) always [1:$] s_eventually b);
  assert property (@(posedge clk) s_always [1:2] s_eventually b);
  assert property (@(posedge clk) a |-> always [0:2] s_eventually b);
  always @(posedge clk) assert property (a |-> always [0:2] s_eventually b);

endmodule
