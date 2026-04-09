// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a, b;
  int n;

  // === Goto repetition [->N] error paths ===

  // Error: non-constant count
  assert property (@(posedge clk) a[->n] |-> b)
    else $error("FAIL");

  // Unsupported: zero count
  assert property (@(posedge clk) a[->0] |-> b)
    else $error("FAIL");

  // Error: negative count
  assert property (@(posedge clk) a[->-1] |-> b)
    else $error("FAIL");

  // === Nonconsecutive repetition [=N] error paths ===

  // Error: non-constant count
  assert property (@(posedge clk) a[=n] |-> b)
    else $error("FAIL");

  // Unsupported: zero count
  assert property (@(posedge clk) a[=0] |-> b)
    else $error("FAIL");

  // Error: negative count
  assert property (@(posedge clk) a[=-1] |-> b)
    else $error("FAIL");

  // === Consecutive repetition [*N] error paths ===

  // Error: non-constant count
  assert property (@(posedge clk) a [*n] |-> 1);

  // Unsupported: [*0] zero repetition
  assert property (@(posedge clk) a [*0] |-> 1);

  // Error: max count < min count
  assert property (@(posedge clk) a [*3:1] |-> 1);

  // Error: non-constant max count
  assert property (@(posedge clk) a [*1:n] |-> 1);

  // Error: [*0:0] zero max count
  assert property (@(posedge clk) a [*0:0] |-> 1);

endmodule
