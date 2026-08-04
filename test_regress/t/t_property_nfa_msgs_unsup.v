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
  int cnt = 0;
  int impure_count = 0;

  property p_nested;
    a ##1 b;
  endproperty

  function automatic bit fimp();
    impure_count++;
    return impure_count[0];
  endfunction

  // Repetition count is not a supported non-negative elaboration-time constant
  assert property (@(posedge clk) a [* 66'd2] |-> b);

  // Repetition maximum is not a supported non-negative elaboration-time constant
  assert property (@(posedge clk) a [* 1: 66'd3] |-> b);

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

  // Fixed-trace expansion diagnostics from the always and throughout paths
  assert property (@(posedge clk) s_always[0: 2000] a);
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

  // Unsupported: abort operator around a branching or unbounded property
  assert property (@(posedge clk) sync_accept_on (a) ((b ##1 c) or(d ##2 e)));

  // Composite sequence operators the count engine cannot lower
  // verilog_format: off
  assert property (@(posedge clk) (a ##1 b) or (c ##2 d));

  cover property (@(posedge clk) (a ##[1:$] b) and (c ##1 d));

  // One done latch cannot identify ranged endpoints for overlapping attempts.
  assert property (@(posedge clk) (a ##[1:2] b) and (c ##2 d));

  assert property (@(posedge clk) (a ##1 b) |-> not (c ##[1:2] d)) $display("pass");

  assert property (@(posedge clk) ((|($random | $random))[*2]) and (1'b1 ##1 1'b1));

  assert property (@(posedge clk) (a[*2000]) and (1'b1 ##1 1'b1));

  assert property (@(posedge clk)
      (s_always [1:2] b) and (((a ##2 b) or (c ##2 d)) ##[1:300] a)) else $display("f");

  assert property (@(posedge clk) ##[1:$] (a until b));
  // verilog_format: on

  // Property if/else control forms the fail-only count engine cannot lower
  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c) $display("pass");
  cover property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);
  assert property (@(posedge clk) not (if (a) 1'b1 ##1 b else 1'b1 ##2 c));

  assert property (@(posedge clk) if (a) s_always[1:2] b else 1'b1 ##1 c);

  assert property (@(posedge clk)
                   if ($random == 0) 1'b1 ##1 b
                   else 1'b1 ##1 c);

  // Huge finite delay bounds are rejected before graph construction
  assert property (@(posedge clk) a ##2147483647 b);
  assert property (@(posedge clk) a ##[0:2147483647] b);
  assert property (@(posedge clk) a ##[1000000000:$] b);

  // Fixed-trace conjunction rejects each non-flattenable operand form
  assert property (@(posedge clk) (a [* 1: $]) and(b ##1 c));
  assert property (@(posedge clk) ((b ##1 c) [* 2]) and(d ##2 e));
  assert property (@(posedge clk) ((a ##[1:2] b) and(c ##1 d)) and(e ##1 a));
  assert property (@(posedge clk) (a throughout ((b ##1 c) or(d ##1 e))) and(c ##2 a));

  // Abort bodies that are not a linear delay chain
  assert property (@(posedge clk) sync_accept_on (a) ((b ##1 c) |-> d));
  assert property (@(posedge clk) sync_accept_on (a) (b ##[1:2] (c ##1 d)));
  assert property (@(posedge clk) sync_accept_on (a) (b ##[1:$] c));
  assert property (@(posedge clk) sync_accept_on (a) (always[0: $] b));
  assert property (@(posedge clk) sync_accept_on (a) (accept_on (b) (c ##1 d)));

  // Variable/unbounded 'and' rejection in a cover context
  cover property (@(posedge clk) (a [-> 1]) and(b [* 2]));

  // Negated delay rings past the ring-bit limit
  assert property (@(posedge clk) not (a ##[1:1200000] b));
  assert property (@(posedge clk) not (a ##[1:66'd9000000000] b));

  // A constant-false always operand still rejects before the shared endpoint
  assert property (@(posedge clk) (always[1: 2] 1'b0) or(c ##2 d));

  // Per-operand rejection inside temporal 'or'
  assert property (@(posedge clk) (a ##2000000 b) or c);
  assert property (@(posedge clk) a or(b ##2000000 c));
  assert property (@(posedge clk) (a ##1 b) or(fimp() ##1 c));
  assert property (@(posedge clk) (b throughout (1'b1 ##2 1'b1)) or(c ##2 d));
  assert property (@(posedge clk) (c ##2 d) or(b throughout (1'b1 ##2 1'b1)));

  // A named property instance nested in a composite is rejected, not dropped
  assert property (@(posedge clk) p_nested or e);

  // Equal-end operands past the shape checks still reject an oversized delay
  assert property (@(posedge clk) (a ##2000000 b) or(c ##2000000 d));
  assert property (@(posedge clk) ((a ##2000000 b) or(c ##2000000 d)) intersect (e ##2000000 a));

  // Abort operators in a multi-cycle property that the count engine rejects
  assert property (@(posedge clk) accept_on (abort_cond) (a ##1 b));

  assert property (@(posedge clk) not (sync_accept_on (abort_cond) (a ##1 b)));

  cover property (@(posedge clk) sync_accept_on (abort_cond) (a ##1 b));

endmodule
