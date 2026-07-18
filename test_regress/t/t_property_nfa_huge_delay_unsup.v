// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Huge finite delay bounds are rejected before any graph or ring construction

module t (
    input clk
);

  bit a = 0, b = 0;

  assert property (@(posedge clk) a ##2147483647 b);
  assert property (@(posedge clk) a ##[0:2147483647] b);
  assert property (@(posedge clk) a ##[1000000000:$] b);

endmodule
