// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a;

  property p_unbounded;
    @(posedge clk) always [2:$] a;
  endproperty

  assert property (p_unbounded);

endmodule
