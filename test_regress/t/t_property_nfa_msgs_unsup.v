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

  sequence s_nested; a ##1 b; endsequence

  function automatic bit fbool();
    return a;
  endfunction

  // Property if/else control the fail-only count engine cannot lower
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c) $display("pass");
  cover property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);
  assert property (@(posedge clk) not (if (a) 1'b1 ##1 b else 1'b1 ##2 c));

  assert property (@(posedge clk) case (a) 1'b0: 1'b1 ##1 b; 1'b1: 1'b1 ##2 c; default: 1'b1 ##1 d;
  endcase)
    $display("pass");

  // An unsupported body under an abort reports itself, not an internal error
  assert property (@(posedge clk) sync_accept_on (a) ((b ##1 c) [* 2]));

  // A body the builder rejects wins over the property if/case message
  assert property (@(posedge clk) if (a) ((b ##1 c)[*2]) else d) $display("pass");

  // A named property instance nested in a composite is rejected, not dropped
  assert property (@(posedge clk) p_nested or e);

  // A named sequence instance is inlined, not rejected
  assert property (@(posedge clk) s_nested or e);

  // A function call is not a property instance
  assert property (@(posedge clk) fbool() ##1 b);

  // A user-written 'and' of implications is not a property if/case
  assert property (@(posedge clk) (a |-> 1'b1 ##1 b) and(c |-> 1'b1 ##2 d));

  // Property if/else without an action is lowered, not rejected
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);

  // A multi-cycle property with no clocking event is left to later passes
  assert property (a [* 2]);

  // An 'and' operand carrying mid-window sources defers to later passes
  assert property (@(posedge clk) (1'b1 ##[1:2] b) and c);

endmodule
