// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a, b;

  // Repetition count exceeds --assert-unroll-limit; pre-fix this hung the
  // compiler, now an error names the limit so the user can raise it.
  assert property (@(posedge clk) a [* 25700000] |-> b);

  // The mandatory prefix of an unbounded repetition is subject to the same limit.
  assert property (@(posedge clk) a [* 25700000:$] |-> b);

endmodule
