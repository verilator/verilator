// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a, b, c, d;
  int delay = 1;

  // Non-constant cycle delay in sequence and/or is unsupported
  assert property (@(posedge clk) (a ##delay b) and (c ##1 d));

endmodule
