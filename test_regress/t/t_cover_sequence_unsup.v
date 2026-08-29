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

  // cover sequence (IEEE 1800-2023 16.14.3) counts every end-of-match. The
  // following forms lack an exact per-end representation, so they are
  // ignored (COVERIGN) rather than under-counted.

  // Ranged cycle delay before a multi-cycle sequence.
  cover sequence (a ##[1:2] (b ##1 c));

  // Ranged cycle delay wider than the unroll limit.
  cover sequence (a ##[1:300] b);

  // Goto repetition coalesces multiple live attempts into one NFA state.
  cover sequence (a [-> 2]);
  cover sequence (a [-> 2: 3]);

endmodule
