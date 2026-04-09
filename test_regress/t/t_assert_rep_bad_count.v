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

endmodule
