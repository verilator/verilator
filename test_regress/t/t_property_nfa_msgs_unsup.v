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
  int cnt = 0;
  int impure_count = 0;

  property p_nested;
    a ##1 b;
  endproperty

  sequence s_nested; a ##1 b; endsequence

  function automatic bit fbool();
    return a;
  endfunction

  function automatic bit fimp();
    impure_count++;
    return impure_count[0];
  endfunction

  // Unsupported: impure expression in a temporal 'or' composite
  assert property (@(posedge clk) (fimp() ##1 a) or(b ##1 c));

  // Unsupported: temporal 'or' endpoint deadline after an operand that can reject earlier
  assert property (@(posedge clk) (s_always[1: 2] a) or(s_always[1: 2] b));

  // Ignoring unsupported: cover sequence with a sequence operand of 'or'
  cover sequence (@(posedge clk) 1'b1 or(a ##1 b));
  cover sequence (@(posedge clk) (a ##1 b) or 1'b1);
  cover sequence (@(posedge clk) (a ##1 b) or(c ##1 d));

  // Unsupported: intersect/within endpoint deadline after an operand that can reject earlier
  assert property (@(posedge clk) (((a ##1 b) or (c ##1 d)) ##1 e) intersect (a throughout (b ##2 c)));

  // Unsupported: impure guard in a flattened throughout composite
  assert property (@(posedge clk) (fimp() throughout (a ##1 b)) and(c ##1 d));

  // Unsupported: impure expression in a flattened temporal composite
  assert property (@(posedge clk) (fimp() ##1 a) and(b ##1 c));

  // Fixed-trace expansion diagnostic from the throughout path
  assert property (@(posedge clk) (a throughout (b ##1024 c)) and(d ##1024 e));

  // Unsupported: property if/case inside a variable-end temporal window
  assert property (@(posedge clk) (a ##[1:$] b) or (if (c) d else e));

  // Unsupported: bounded temporal 'and' operand cannot be represented as a fixed trace
  assert property (@(posedge clk) ((a ##1 b) or(c ##1 d)) and(e ##1 a));

  // Unsupported: strong s_always in a temporal AND/intersect composite
  assert property (@(posedge clk) (((a ##1 b) or (c ##1 d)) intersect (e ##1 a)) |-> s_always [1:2] b);

  // Unsupported multiple strong operators with ambiguous EOS attempt depth
  assert property (@(posedge clk) ((a ##1 b) or(c ##1 d)) ##1 (e [-> 1]) |-> s_always[1: 2] a);

  // Multiple strong operators require too many EOS ring slots
  assert property (@(posedge clk) ((a ##1 b) or(c ##1 d)) |-> s_always[1030: 1030] e) cnt++;

  // Unsupported: strong s_always pending state has a non-positive temporal depth
  assert property (@(posedge clk) ((a ##1 b) or(c ##1 d)) |-> s_always[0: 0] e) cnt++;

  // Unsupported strong pass multiplicity when temporal OR loses resolved attempts
  assert property (@(posedge clk) a |-> (((a ##1 b) or(c ##1 d)) |-> s_always[1: 2] e)) cnt++;

  // Composite sequence operators the count engine cannot lower
  // verilog_format: off
  assert property (@(posedge clk) (a ##1 b) or (c ##2 d));

  cover property (@(posedge clk) (a ##[1:$] b) and (c ##1 d));

  // One done latch cannot identify ranged endpoints for overlapping attempts.
  assert property (@(posedge clk) (a ##[1:2] b) and (c ##2 d));

  assert property (@(posedge clk) (a ##1 b) |-> not (c ##[1:2] d)) $display("pass");

  assert property (@(posedge clk) ((|($random | $random))[*2]) and (1'b1 ##1 1'b1));
  assert property (@(posedge clk) ((|($urandom | $urandom))[*2]) and (1'b1 ##1 1'b1));

  assert property (@(posedge clk) (a[*2000]) and (1'b1 ##1 1'b1));

  assert property (@(posedge clk)
      (s_always [1:2] b) and (((a ##2 b) or (c ##2 d)) ##[1:300] a)) else $display("f");

  assert property (@(posedge clk) ##[1:$] (a until b));
  // verilog_format: on

  // Property if/else control the fail-only count engine cannot lower
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c) $display("pass");
  cover property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);
  assert property (@(posedge clk) not (if (a) 1'b1 ##1 b else 1'b1 ##2 c));

  assert property (@(posedge clk) case (a) 1'b0: 1'b1 ##1 b; 1'b1: 1'b1 ##2 c; default: 1'b1 ##1 d;
  endcase)
    $display("pass");

  assert property (@(posedge clk) if (a) s_always[1:2] b else 1'b1 ##1 c);

  assert property (@(posedge clk)
                   if ($random == 0) 1'b1 ##1 b
                   else 1'b1 ##1 c);

  // An unsupported body under an abort reports itself, not an internal error
  assert property (@(posedge clk) sync_accept_on (a) ((b ##1 c) [* 2]));

  // A body the builder rejects wins over the property if/case message
  assert property (@(posedge clk) if (a) ((b ##1 c)[*2]) else d) $display("pass");

  // Fixed-trace conjunction rejects each non-flattenable operand form
  assert property (@(posedge clk) (a [* 1: $]) and(b ##1 c));
  assert property (@(posedge clk) ((b ##1 c) [* 2]) and(d ##2 e));
  assert property (@(posedge clk) ((a ##[1:2] b) and(c ##1 d)) and(e ##1 a));
  assert property (@(posedge clk) (a throughout ((b ##1 c) or(d ##1 e))) and(c ##2 a));

  // Variable/unbounded 'and' rejection in a cover context
  cover property (@(posedge clk) (a [-> 1]) and(b [* 2]));

  // Per-operand rejection inside temporal 'or'
  assert property (@(posedge clk) (a ##1 b) or(fimp() ##1 c));
  assert property (@(posedge clk) (b throughout (1'b1 ##2 1'b1)) or(c ##2 d));
  assert property (@(posedge clk) (c ##2 d) or(b throughout (1'b1 ##2 1'b1)));

  // Nested fixed-trace conjunctions reject through the enclosing operator
  assert property (@(posedge clk) (((a ##1 b) or(c ##1 d)) and(e ##1 a)) and(b ##1 c));
  assert property (@(posedge clk) ((fimp() ##1 a) and(b ##1 c)) and(d ##1 e));
  assert property (@(posedge clk) (a ##1 b) and(fimp() ##1 c));
  assert property (@(posedge clk) (##1 fimp()) and(b ##1 c));
  assert property (@(posedge clk) (((a ##1 b) or(c ##1 d)) and(e ##1 a)) or(b ##1 c));
  assert property (@(posedge clk) (b ##1 c) or(((a ##1 b) or(c ##1 d)) and(e ##1 a)));
  assert property (@(posedge clk) (a ##2 b) intersect ((fimp() ##2 c) or(d ##2 e)));
  assert property (@(posedge clk) (a ##[1:2] b) and((fimp() ##1 c) or(d ##1 e)));
  assert property (@(posedge clk) ((fimp() ##1 c) or(d ##1 e)) and(a ##[1:2] b));

  // Variable-length repetition operands of a temporal 'or'
  assert property (@(posedge clk) ((a [* 1: 2]) and(b ##1 c)) or(d ##1 e));
  assert property (@(posedge clk) ((a ##1 b) and(c [* 1: 2])) or(d ##1 e));

  // A sequence operand of 'until', a throughout body the builder rejects, if/case under an abort
  assert property (@(posedge clk) (a ##1 b) until c);
  assert property (@(posedge clk) a throughout ((b ##1 c) [* 2]));
  assert property (@(posedge clk) sync_accept_on (a) (if (b) 1'b1 ##1 c else 1'b1 ##2 d));
  cover property (@(posedge clk) (a ##1 b) |-> not (c ##[1:2] d));

  // A named property instance nested in a composite is rejected, not dropped
  assert property (@(posedge clk) p_nested or e);

  // A named sequence instance is inlined, not rejected
  assert property (@(posedge clk) s_nested or(c ##1 d));

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
  assert property (@(posedge clk) c and(1'b1 ##[1:2] b));

  // A boolean 'and' operand of a rejected cover-sequence 'or' is freed
  cover sequence (@(posedge clk) ((a and b) or(c ##1 d)));

  // A constant strong 'or' operand is not folded
  assert property (@(posedge clk) (s_always [1:2] 1'b1) or(a ##2 b));

  // A constant-true 'or' operand of a cover sequence folds away
  cover sequence (@(posedge clk) (1'b1 or c) ##1 d);
  cover sequence (@(posedge clk) (c or 1'b1) ##1 d);

  // A nonconsecutive repetition operand of 'or' is diagnosed at the 'or'
  assert property (@(posedge clk) (a [= 1] ##1 b) or(c ##2 d));
  assert property (@(posedge clk) (c ##2 d) or(a [= 1] ##1 b));

  // An 'or' under intersect in a cover property is lowered
  cover property (@(posedge clk) (a ##2 b) intersect ((c ##2 d) or(e ##2 a)));

  // An unbounded 'and' operand is lowered through the combiner
  assert property (@(posedge clk) (a ##[1:$] b) and(c ##1 d));

  // A nested 'and' whose right operand cannot be flattened
  assert property (@(posedge clk) ((a ##1 b) and((c ##1 d) or(e ##1 a))) and(b ##1 c));
  assert property (@(posedge clk) ((a ##1 b) and(fimp() ##1 c)) and(d ##1 e));

  // Property if/else with a boolean else branch is lowered
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else c);

  // A fixed-count repetition range and a four-state constant operand are lowered
  assert property (@(posedge clk) (a [* 2: 2]) and(b ##1 c));
  assert property (@(posedge clk) (always [1:2] 1'bx) or(a ##2 b));

  // Left-operand mirrors of the intersect rejections
  assert property (@(posedge clk) (a throughout ((b ##2 c) or(d ##2 e))) intersect (c ##2 a));
  assert property (@(posedge clk) ((fimp() ##2 c) or(d ##2 e)) intersect (a ##2 b));

endmodule
