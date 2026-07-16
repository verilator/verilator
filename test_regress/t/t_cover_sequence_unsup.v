// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  logic a, b, c;

  default clocking cb @(posedge clk);
  endclocking

  // Ignore cover sequences that lack an exact per-end representation (IEEE 16.14.3).

  // Ranged cycle delay before a multi-cycle sequence.
  cover sequence (a ##[1:2] (b ##1 c));

  // Ranged cycle delay wider than the unroll limit.
  cover sequence (a ##[1:300] b);

  // Ranged goto repetition.
  cover sequence (a [-> 2: 3]);

endmodule
