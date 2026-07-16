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

endmodule
