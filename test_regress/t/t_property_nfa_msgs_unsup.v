// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Each property exercises one unsupported-diagnostic path of the NFA lowering

module t (
    input clk
);

  bit a = 0, b = 0, c = 0, d = 0, e = 0;

  property p_nested;
    a ##1 b;
  endproperty

  // Property if/else control the fail-only count engine cannot lower
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c) $display("pass");
  cover property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);
  assert property (@(posedge clk) not (if (a) 1'b1 ##1 b else 1'b1 ##2 c));

  assert property (@(posedge clk)
                   case (a) 1'b0: 1'b1 ##1 b; 1'b1: 1'b1 ##2 c; default: 1'b1 ##1 d; endcase)
    $display("pass");

  // Abort around an implication crashes the lowering
  assert property (@(posedge clk) sync_accept_on (a) (b |-> c));
  assert property (@(posedge clk) sync_accept_on (a) ((b ##1 c) |-> d));
  assert property (@(posedge clk) accept_on (a) (b |=> c));
  assert property (@(posedge clk) sync_accept_on (a) ((b |-> c) or d));
  assert property (@(posedge clk) sync_accept_on (a) (d or (b |-> c)));

  // A named property instance nested in a composite is rejected, not dropped
  assert property (@(posedge clk) p_nested or e);

  // Abort bodies without a bare implication are lowered, not rejected
  assert property (@(posedge clk) sync_accept_on (a) (not (b |-> c)));
  assert property (@(posedge clk) sync_accept_on (a) (b or c));

  // A user-written 'and' of implications is not a property if/case
  assert property (@(posedge clk) (a |-> 1'b1 ##1 b) and (c |-> 1'b1 ##2 d));

  // Property if/else without an action is lowered, not rejected
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);

endmodule
