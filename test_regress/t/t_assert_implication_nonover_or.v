// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Brambilla
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a = 0, x = 0, y = 0, a2 = 0, x2 = 0, y2 = 0, a3 = 0, x3 = 0, y3 = 0;
  int fail_or = 0, fail_or_noparen = 0, fail_prop_or = 0, fail_multi_ante = 0;
  int fail_delay_or = 0, fail_and = 0;
  int cov_prop_or = 0, cov_prop_lor = 0, cov_seq_or = 0, cov_seq_lor = 0;
  int pass_top_or = 0, fail_top_or = 0, pass_top_not_or = 0, fail_top_not_or = 0;
  int fail_rep0 = 0, fail_rep1 = 0, fail_nonbool_l = 0, fail_nonbool_l2 = 0, fail_nonbool_r = 0;

  // a in cycles 3, 6, 9, 12; the consequent cycle after each has
  //   cycle 4: x=0 y=0 -> every disjunction fails
  //   cycle 7: x=1 y=0, cycle 10: x=0 y=1, cycle 13: x=1 y=1 -> no disjunction fails
  assert property (@(posedge clk) a |=> (x || y))
  else fail_or = fail_or + 1;
  assert property (@(posedge clk) a |=> x || y)
  else fail_or_noparen = fail_or_noparen + 1;
  assert property (@(posedge clk) a |=> (x or y))
  else fail_prop_or = fail_prop_or + 1;
  assert property (@(posedge clk) a ##1 1 |-> (x || y))
  else fail_multi_ante = fail_multi_ante + 1;
  assert property (@(posedge clk) a |-> ##1 (x || y))
  else fail_delay_or = fail_delay_or + 1;
  assert property (@(posedge clk) a |=> (x && y))
  else fail_and = fail_and + 1;

  // A top-level disjunction must reject too; 'not' of it fails where it holds
  assert property (@(posedge clk) x or y) pass_top_or = pass_top_or + 1;
  else fail_top_or = fail_top_or + 1;
  assert property (@(posedge clk) not (x or y)) pass_top_not_or = pass_top_not_or + 1;
  else fail_top_not_or = fail_top_not_or + 1;

  // Antecedents with a consecutive repetition. a2 is true only in cycle 15 and x2 in cycle 16,
  // so every real match holds; the empty matches of a2[*0:2] must not start the consequent
  assert property (@(posedge clk) a2 [* 0:2] |=> (x2 or y2))
  else fail_rep0 = fail_rep0 + 1;
  // a is true in cycles 3, 6, 9, 12: a[*1:2] fails once, in cycle 4
  assert property (@(posedge clk) a [* 1:2] |=> (x or y))
  else fail_rep1 = fail_rep1 + 1;

  // An operand that is not a plain boolean keeps the merge vertex. a3 is true in cycle 17
  // and y3 in cycle 18, so each holds and nothing may be reported.
  assert property (@(posedge clk) a3 |=> ((not (x3 |-> y3)) or y3))
  else fail_nonbool_l = fail_nonbool_l + 1;
  assert property (@(posedge clk) a3 |=> ((not (x3 |=> y3)) or y3))
  else fail_nonbool_l2 = fail_nonbool_l2 + 1;
  assert property (@(posedge clk) a3 |=> (y3 or (not (x3 |-> y3))))
  else fail_nonbool_r = fail_nonbool_r + 1;

  // x or y is true in cycles 7, 10 and 13
  cover property (@(posedge clk) x or y) cov_prop_or = cov_prop_or + 1;
  cover property (@(posedge clk) x || y) cov_prop_lor = cov_prop_lor + 1;
  cover sequence (@(posedge clk) x or y) cov_seq_or = cov_seq_or + 1;
  cover sequence (@(posedge clk) x || y) cov_seq_lor = cov_seq_lor + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= (cyc == 2 || cyc == 5 || cyc == 8 || cyc == 11);
    x <= (cyc == 6 || cyc == 12);
    y <= (cyc == 9 || cyc == 12);
    a2 <= (cyc == 14);
    x2 <= (cyc == 15);
    a3 <= (cyc == 16);
    y3 <= (cyc == 17);
    if (cyc == 20) begin
      `checkd(fail_or, 1);
      `checkd(fail_or_noparen, 1);
      `checkd(fail_prop_or, 1);
      `checkd(fail_multi_ante, 1);
      `checkd(fail_delay_or, 1);
      `checkd(fail_and, 3);
      `checkd(cov_prop_or, 3);
      `checkd(cov_prop_lor, 3);
      `checkd(cov_seq_or, 3);
      `checkd(cov_seq_lor, 3);
      `checkd(pass_top_or, 3);
      `checkd(fail_top_or, 17);
      `checkd(pass_top_not_or, 17);
      `checkd(fail_top_not_or, 3);
      `checkd(fail_rep0, 0);
      `checkd(fail_rep1, 1);
      `checkd(fail_nonbool_l, 0);
      `checkd(fail_nonbool_l2, 0);
      `checkd(fail_nonbool_r, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
