// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a;

  // Bad: standalone range repetition (no ## delay to anchor the sequence)
  assert property (@(posedge clk) a [*2:3] |-> 1);

endmodule
