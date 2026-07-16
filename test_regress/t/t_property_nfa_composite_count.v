// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Directed per-attempt count checks for composite sequence operators.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit or_fail_start = 0;
  bit or_both_start = 0;
  int or_fail_pass = 0;
  int or_fail_count = 0;
  int or_both_pass = 0;
  int or_both_fail = 0;

  assert property (@(posedge clk) or_fail_start |-> ((1'b1 ##1 1'b0) or(1'b1 ##1 1'b0)))
    or_fail_pass++;
  else or_fail_count++;

  assert property (@(posedge clk) or_both_start |-> ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b1)))
    or_both_pass++;
  else or_both_fail++;

  bit cross_l_start = 0;
  bit cross_l_end = 0;
  bit cross_r_start = 0;
  bit cross_r_end = 0;
  int cross_hits = 0;

  cover property (@(posedge clk) (cross_l_start ##1 cross_l_end) and(cross_r_start ##2 cross_r_end))
    cross_hits++;

  bit throughout_start = 0;
  bit throughout_guard = 0;
  int throughout_pass = 0;
  int throughout_fail = 0;

  assert property (@(posedge clk) throughout_start |->
      ((throughout_guard throughout (1'b1 ##2 1'b1)) and
       (1'b1 ##1 1'b1)))
    throughout_pass++;
  else throughout_fail++;

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

    // Cross-attempt SAnd stimulus.
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

    // One failed throughout/SAnd attempt.
    throughout_guard = 1;
    throughout_start = 1;
    @(negedge clk);
    throughout_start = 0;
    throughout_guard = 0;
    repeat (3) @(negedge clk);

    // One successful throughout/SAnd attempt.
    throughout_guard = 1;
    throughout_start = 1;
    @(negedge clk);
    throughout_start = 0;
    repeat (3) @(negedge clk);

    `checkd(or_fail_pass, 0);
    `checkd(or_fail_count, 1);
    `checkd(or_both_pass, 1);
    `checkd(or_both_fail, 0);
    `checkd(cross_hits, 0);
    `checkd(throughout_pass, 1);
    `checkd(throughout_fail, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
