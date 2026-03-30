// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a;
  int n;

  // Bad: non-constant repetition count
  assert property (@(posedge clk) a [* n] |-> 1);

  // Bad: [*0] consecutive repetition unsupported
  assert property (@(posedge clk) a [* 0] |-> 1);

endmodule
