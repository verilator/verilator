// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a, b, c, d;

  default clocking @(posedge clk);
  endclocking

  // LHS length in [1,2], RHS in [4,5]: no common length, can never match
  assert property ((a ##[1:2] b) intersect (c ##[4:5] d));

endmodule
