// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a, b;

  // === Consecutive repetition [*N] unsupported forms ===

  // Unsupported: non-##1 inter-repetition delay
  assert property (@(posedge clk) a [*2] ##3 b);

  // Unsupported: standalone range repetition (no ## anchor)
  assert property (@(posedge clk) a [*2:3] |-> 1);

  // Unsupported: trailing consecutive repetition in sequence
  assert property (@(posedge clk) b ##1 a[+]);

  // === Nonconsecutive repetition [=N] unsupported forms ===

  // Unsupported: nonconsecutive rep inside throughout
  assert property (@(posedge clk) a throughout (b[=2]))
    else $error("FAIL");

endmodule
