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
  // following forms put a sub-sequence where only its final end is forwarded,
  // so they are ignored (COVERIGN) rather than under-counted.

  // Sequence operand of 'or' (ranged cycle delay).
  cover sequence ((a ##[1:3] b) or 1'b0);

  // Sequence operand of 'or' (consecutive repetition).
  cover sequence ((a [* 1: 3]) or 1'b0);

  // Ranged cycle delay before a multi-cycle sequence.
  cover sequence (a ##[1:2] (b ##1 c));

  // Ranged cycle delay wide enough to use the counter FSM.
  cover sequence (a ##[1:300] b);

  // Ranged goto repetition (every M..N-th match is a separate end).
  cover sequence (a [-> 2: 3]);

endmodule
