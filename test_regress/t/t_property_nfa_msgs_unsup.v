// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Each property exercises one unsupported-diagnostic path of the NFA lowering

module t (
    input clk
);

  bit a = 0, b = 0, c = 0, d = 0, e = 0, abort_cond = 0;

  property p_nested;
    a ##1 b;
  endproperty

  // Property if/else control forms the fail-only count engine cannot lower
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c) $display("pass");
  cover property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);
  assert property (@(posedge clk) not (if (a) 1'b1 ##1 b else 1'b1 ##2 c));

  assert property (@(posedge clk) if (a) s_always [1:2] b else 1'b1 ##1 c);

  // Abort bodies that are not a linear delay chain
  assert property (@(posedge clk) sync_accept_on (a) ((b ##1 c) |-> d));
  assert property (@(posedge clk) sync_accept_on (a) (b ##[1:2] (c ##1 d)));
  assert property (@(posedge clk) sync_accept_on (a) (b ##[1:$] c));
  assert property (@(posedge clk) sync_accept_on (a) (always [0:$] b));
  assert property (@(posedge clk) sync_accept_on (a) (accept_on (b) (c ##1 d)));

  // A named property instance nested in a composite is rejected, not dropped
  assert property (@(posedge clk) p_nested or e);

  // Abort operators in a multi-cycle property that the count engine rejects
  assert property (@(posedge clk) accept_on (abort_cond) (a ##1 b));

  assert property (@(posedge clk) not (sync_accept_on (abort_cond) (a ##1 b)));

  cover property (@(posedge clk) sync_accept_on (abort_cond) (a ##1 b));

endmodule
