// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Abort operators in a multi-cycle property that the count engine rejects.

module t (
    input clk
);

  bit a;
  bit b;
  bit abort_cond;

  assert property (@(posedge clk) accept_on (abort_cond) (a ##1 b));

  assert property (@(posedge clk) not (sync_accept_on (abort_cond) (a ##1 b)));

  cover property (@(posedge clk) sync_accept_on (abort_cond) (a ##1 b));

endmodule
