// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a;
  int n;

  // Bad: non-constant repetition count
  assert property (@(posedge clk) a [*n] |-> 1);

  // Bad: [*0] unsupported exact zero repetition
  assert property (@(posedge clk) a [*0] |-> 1);

  // Bad: max count < min count
  assert property (@(posedge clk) a [*3:1] |-> 1);

  // Bad: non-constant max count
  assert property (@(posedge clk) a [*1:n] |-> 1);

  // Bad: [*N:0] zero max count
  assert property (@(posedge clk) a [*0:0] |-> 1);

endmodule
