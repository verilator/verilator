// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
// verilog_lint: off
// verilog_format: on

module t (input clk);
  logic a, b, c, d;

  // LHS length 2, RHS length 4 -- WIDTHTRUNC (left < right)
  assert property (@(posedge clk)
      (a ##1 b) intersect (c ##3 d));

  // LHS length 4, RHS length 2 -- WIDTHEXPAND (left > right)
  assert property (@(posedge clk)
      (a ##3 b) intersect (c ##1 d));

endmodule
