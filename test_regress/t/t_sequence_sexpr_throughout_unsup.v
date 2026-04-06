// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
  input clk
);
  logic a, b, c;

  // Unsupported: throughout with range delay on RHS (IEEE 16.9.9)
  assert property (@(posedge clk)
      a |-> (a throughout (b ##[1:2] c)));

  // Unsupported: throughout with temporal 'and' sequence on RHS
  assert property (@(posedge clk)
      a |-> (a throughout ((b ##1 c) and (c ##1 b))));

  // Unsupported: nested throughout
  assert property (@(posedge clk)
      a |-> (a throughout (b throughout (b ##1 c))));

endmodule
