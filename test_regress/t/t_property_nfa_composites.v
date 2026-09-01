// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Per-attempt counts for composite sequence operators.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  // Common-end sequence OR
  bit or_fail_start = 0, or_both_start = 0;
  int or_fail_pass = 0, or_fail_count = 0;
  int or_both_pass = 0, or_both_fail = 0;

  assert property (@(posedge clk) or_fail_start |-> ((1'b1 ##1 1'b0) or(1'b1 ##1 1'b0)))
    or_fail_pass++;
  else or_fail_count++;

  assert property (@(posedge clk) or_both_start |-> ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b1)))
    or_both_pass++;
  else or_both_fail++;

  // Cross-attempt sequence AND
  bit cross_l_start = 0, cross_l_end = 0, cross_r_start = 0, cross_r_end = 0;
  int cross_hits = 0;

  cover property (@(posedge clk) (cross_l_start ##1 cross_l_end) and(cross_r_start ##2 cross_r_end))
    cross_hits++;

  // Throughout guard composed with sequence AND
  bit throughout_start = 0, throughout_guard = 0;
  int throughout_pass = 0, throughout_fail = 0;

  assert property (@(posedge clk) throughout_start |->
      ((throughout_guard throughout (1'b1 ##2 1'b1)) and
       (1'b1 ##1 1'b1)))
    throughout_pass++;
  else throughout_fail++;

  // Same-end intersect over branching left operands
  int isect_pass_one = 0, isect_pass_both = 0, isect_pass_zero = 0;
  int isect_fail_left = 0, isect_fail_right = 0, isect_fail_zero = 0;
  int isect_unexp_one = 0, isect_unexp_both = 0, isect_unexp_zero_pass = 0;
  int isect_unexp_zero_fail = 0, isect_unexp_left = 0, isect_unexp_right = 0;

  assert property (@(posedge clk) ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b0)) intersect (1'b1 ##1 1'b1))
    isect_pass_one <= isect_pass_one + 1;
  else isect_unexp_one <= isect_unexp_one + 1;

  assert property (@(posedge clk) ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b1)) intersect (1'b1 ##1 1'b1))
    isect_pass_both <= isect_pass_both + 1;
  else isect_unexp_both <= isect_unexp_both + 1;

  assert property (@(posedge clk) (1'b1 or 1'b0) intersect 1'b1)
    isect_pass_zero <= isect_pass_zero + 1;
  else isect_unexp_zero_pass <= isect_unexp_zero_pass + 1;

  assert property (@(posedge clk) (1'b0 or 1'b0) intersect 1'b1)
    isect_unexp_zero_fail <= isect_unexp_zero_fail + 1;
  else isect_fail_zero <= isect_fail_zero + 1;

  assert property (@(posedge clk) ((1'b1 ##1 1'b0) or(1'b1 ##1 1'b0)) intersect (1'b1 ##1 1'b1))
    isect_unexp_left <= isect_unexp_left + 1;
  else isect_fail_left <= isect_fail_left + 1;

  assert property (@(posedge clk) ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b0)) intersect (1'b1 ##1 1'b0))
    isect_unexp_right <= isect_unexp_right + 1;
  else isect_fail_right <= isect_fail_right + 1;

  initial begin
    $assertpasson;
    $assertvacuousoff;

    repeat (2) @(negedge clk);

    // Common-end OR stimulus
    or_fail_start = 1;
    or_both_start = 1;
    @(negedge clk);
    or_fail_start = 0;
    or_both_start = 0;
    repeat (2) @(negedge clk);

    // Cross-attempt SAnd stimulus
    cross_l_start = 1;
    cross_r_start = 1;
    @(negedge clk);
    cross_l_start = 1;
    cross_l_end = 0;
    cross_r_start = 0;
    cross_r_end = 0;
    @(negedge clk);
    cross_l_start = 0;
    cross_l_end = 1;
    cross_r_start = 0;
    cross_r_end = 1;
    @(negedge clk);
    cross_l_end = 0;
    cross_r_end = 0;
    repeat (2) @(negedge clk);

    // One failed throughout/SAnd attempt
    throughout_guard = 1;
    throughout_start = 1;
    @(negedge clk);
    throughout_start = 0;
    throughout_guard = 0;
    repeat (3) @(negedge clk);

    // One successful throughout/SAnd attempt
    throughout_guard = 1;
    throughout_start = 1;
    @(negedge clk);
    throughout_start = 0;
    repeat (3) @(negedge clk);

    `checkd(or_fail_pass, 0);
    `checkd(or_fail_count, 0);
    `checkd(or_both_pass, 1);
    `checkd(or_both_fail, 0);
    `checkd(cross_hits, 0);
    `checkd(throughout_pass, 1);
    `checkd(throughout_fail, 1);
    `checkd(isect_pass_one, 17);
    `checkd(isect_pass_both, 17);
    `checkd(isect_pass_zero, 18);
    `checkd(isect_fail_left, 0);
    `checkd(isect_fail_right, 17);
    `checkd(isect_fail_zero, 18);
    `checkd(isect_unexp_one, 0);
    `checkd(isect_unexp_both, 0);
    `checkd(isect_unexp_zero_pass, 0);
    `checkd(isect_unexp_zero_fail, 0);
    `checkd(isect_unexp_left, 0);
    `checkd(isect_unexp_right, 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
