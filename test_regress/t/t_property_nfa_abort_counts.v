// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Per-attempt abort outcomes: windowed implication, negated body, vacuous passes.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit large_a = 0, large_b = 0, large_abort = 0, large_disable = 0;
  int large_accept_pass = 0, large_accept_fail = 0;
  int large_reject_pass = 0, large_reject_fail = 0;
  int large_disable_accept_pass = 0, large_disable_accept_fail = 0;

  bit b = 0, abort_cond = 0, abort_a = 0, never_abort = 0;
  int accept_pass_at_abort = 0, accept_fail_at_abort = 0;
  int reject_pass_at_abort = 0, reject_fail_at_abort = 0;
  int plain_vacuous_pass = 0, wrapped_vacuous_pass = 0;
  int negated_plain_vacuous_pass = 0, negated_wrapped_vacuous_pass = 0;

  initial $assertpasson;

  assert property (@(posedge clk) sync_accept_on (large_abort) (large_a |-> ##[1:300] large_b)) begin
    if (large_abort) large_accept_pass++;
  end
  else if (large_abort) large_accept_fail++;
  assert property (@(posedge clk) sync_reject_on (large_abort) (large_a |-> ##[1:300] large_b)) begin
    if (large_abort) large_reject_pass++;
  end
  else if (large_abort) large_reject_fail++;
  assert property (@(posedge clk) disable iff (large_disable)
                   sync_accept_on (large_abort) (large_a |-> ##[1:300] large_b)) begin
    if (large_abort) large_disable_accept_pass++;
  end
  else if (large_abort) large_disable_accept_fail++;

  // Abort outcome is outside `not`: accept stays a pass, reject stays a failure.
  assert property (@(posedge clk) sync_accept_on (abort_cond) (abort_a |-> not (##[1:300] b))) begin
    if (abort_cond) accept_pass_at_abort++;
  end
  else begin
    if (abort_cond) accept_fail_at_abort++;
  end
  assert property (@(posedge clk) sync_reject_on (abort_cond) (abort_a |-> not (##[1:300] b))) begin
    if (abort_cond) reject_pass_at_abort++;
  end
  else begin
    if (abort_cond) reject_fail_at_abort++;
  end

  // A false outer abort must not suppress the vacuous pass action.
  assert property (@(posedge clk) 0 |-> ##1 1) plain_vacuous_pass++;
  assert property (@(posedge clk) sync_accept_on (never_abort) (0 |-> ##1 1))
    wrapped_vacuous_pass++;
  assert property (@(posedge clk) 0 |-> not (##1 1)) negated_plain_vacuous_pass++;
  assert property (@(posedge clk) sync_accept_on (never_abort) (0 |-> not (##1 1)))
    negated_wrapped_vacuous_pass++;

  initial begin
    @(negedge clk) begin
      large_a = 1;
      abort_a = 1;
    end
    @(negedge clk) begin
      large_a = 1;
      abort_a = 1;
    end
    @(negedge clk) begin
      large_a = 0;
      large_b = 1;
      large_abort = 1;
      b = 1;
      abort_cond = 1;
      abort_a = 1;
    end
    @(negedge clk) begin
      large_b = 0;
      large_abort = 0;
      b = 0;
      abort_cond = 0;
      `checkd(large_accept_pass, 3);
      `checkd(large_accept_fail, 0);
      `checkd(large_reject_pass, 0);  // Other simulator: 1
      `checkd(large_reject_fail, 3);  // Other simulator: 2
      `checkd(large_disable_accept_pass, 3);
      `checkd(large_disable_accept_fail, 0);
      `checkd(accept_pass_at_abort, 3);
      `checkd(accept_fail_at_abort, 0);
      `checkd(reject_pass_at_abort, 0);
      `checkd(reject_fail_at_abort, 3);
      `checkd(plain_vacuous_pass, 4);
      `checkd(wrapped_vacuous_pass, 4);
      `checkd(negated_plain_vacuous_pass, 4);
      `checkd(negated_wrapped_vacuous_pass, 4);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
