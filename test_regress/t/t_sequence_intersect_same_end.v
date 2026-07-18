// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Same-end intersect counts one verdict per assertion attempt.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int pass_one = 0;
  int pass_both = 0;
  int pass_zero = 0;
  int fail_left = 0;
  int fail_right = 0;
  int fail_zero = 0;
  int unexpected_one = 0;
  int unexpected_both = 0;
  int unexpected_zero_pass = 0;
  int unexpected_zero_fail = 0;
  int unexpected_left = 0;
  int unexpected_right = 0;

  assert property (@(posedge clk) ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b0)) intersect (1'b1 ##1 1'b1))
    pass_one <= pass_one + 1;
  else unexpected_one <= unexpected_one + 1;

  assert property (@(posedge clk) ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b1)) intersect (1'b1 ##1 1'b1))
    pass_both <= pass_both + 1;
  else unexpected_both <= unexpected_both + 1;

  assert property (@(posedge clk) (1'b1 or 1'b0) intersect 1'b1) pass_zero <= pass_zero + 1;
  else unexpected_zero_pass <= unexpected_zero_pass + 1;

  assert property (@(posedge clk) (1'b0 or 1'b0) intersect 1'b1)
    unexpected_zero_fail <= unexpected_zero_fail + 1;
  else fail_zero <= fail_zero + 1;

  assert property (@(posedge clk) ((1'b1 ##1 1'b0) or(1'b1 ##1 1'b0)) intersect (1'b1 ##1 1'b1))
    unexpected_left <= unexpected_left + 1;
  else fail_left <= fail_left + 1;

  assert property (@(posedge clk) ((1'b1 ##1 1'b1) or(1'b1 ##1 1'b0)) intersect (1'b1 ##1 1'b0))
    unexpected_right <= unexpected_right + 1;
  else fail_right <= fail_right + 1;

  initial begin
    repeat (6) @(negedge clk);
    `checkd(pass_one, 5);
    `checkd(pass_both, 5);
    `checkd(pass_zero, 6);
    `checkd(fail_left, 5);
    `checkd(fail_right, 5);
    `checkd(fail_zero, 6);
    `checkd(unexpected_one, 0);
    `checkd(unexpected_both, 0);
    `checkd(unexpected_zero_pass, 0);
    `checkd(unexpected_zero_fail, 0);
    `checkd(unexpected_left, 0);
    `checkd(unexpected_right, 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
