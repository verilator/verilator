// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Per-attempt counts for negated properties, aborts, and vacuous passes.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit a = 0;
  bit b = 0;
  int fail_at_b = 0;
  int large_fail_at_b = 0;
  bit chain_a = 0;
  bit chain_b = 0;
  bit chain_c = 0;
  bit chain_target = 0;
  int pass_at_chain_target = 0;
  int fail_at_chain_target = 0;
  int cover_at_chain_target = 0;
  bit implication_a = 0;
  bit implication_b = 0;
  bit implication_c = 0;
  bit implication_target = 0;
  int implication_pass_at_target = 0;
  bit abort_cond = 0;
  bit abort_a = 0;
  int accept_pass_at_abort = 0;
  int accept_fail_at_abort = 0;
  int reject_pass_at_abort = 0;
  int reject_fail_at_abort = 0;
  bit never_abort = 0;
  int plain_vacuous_pass = 0;
  int wrapped_vacuous_pass = 0;
  int negated_plain_vacuous_pass = 0;
  int negated_wrapped_vacuous_pass = 0;

  assert property (@(posedge clk) not (a ##[1:2] b))
  else if (b) fail_at_b++;
  // The same multiplicity through the large-range ring-buffer path.
  assert property (@(posedge clk) not (a ##[1:300] b))
  else if (b) large_fail_at_b++;

  // Negation swaps each attempt's rejects and match at chain_target
  assert property (@(posedge clk) not (chain_a ##1 chain_b ##1 chain_c)) begin
    if (chain_target) pass_at_chain_target++;
  end
  else begin
    if (chain_target) fail_at_chain_target++;
  end
  cover property (@(posedge clk) not (chain_a ##1 chain_b ##1 chain_c))
    if (chain_target) cover_at_chain_target++;

  // One nonvacuous and one vacuous pass in the same clock.
  assert property (@(posedge clk) implication_a |-> not (implication_b ##1 implication_c))
    if (implication_target) implication_pass_at_target++;

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
      a = 1;
      chain_a = 1;
      implication_a = 1;
      implication_b = 1;
      abort_a = 1;
    end
    @(negedge clk) begin
      a = 1;
      chain_a = 1;
      chain_b = 1;
      implication_a = 0;
      implication_b = 0;
      implication_target = 1;
      abort_a = 1;
    end
    @(negedge clk) begin
      a = 0;
      b = 1;
      chain_a = 0;
      chain_b = 0;
      chain_c = 1;
      chain_target = 1;
      implication_target = 0;
      abort_cond = 1;
      abort_a = 1;
    end
    @(negedge clk) begin
      b = 0;
      chain_target = 0;
      abort_cond = 0;
      `checkd(fail_at_b, 2);
      `checkd(large_fail_at_b, 2);
      `checkd(pass_at_chain_target, 2);
      `checkd(fail_at_chain_target, 1);
      `checkd(cover_at_chain_target, 2);
      `checkd(implication_pass_at_target, 2);
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
