// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  int x;
  logic a;

  default clocking cb @(posedge clk); endclocking

  assert property (always [-1:3] a);
  assert property (always [5:2] a);
  assert property (always [x:3] a);
  assert property (always [1:x] a);
  assert property (s_always a);
  assert property (s_always [1:$] a);

endmodule
