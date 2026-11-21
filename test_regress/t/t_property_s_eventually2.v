// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define PROPERTY_CHECK(msg) \
    $display("[%0t] stmt, %s", $time, msg); \
  else \
    $display("[%0t] else, %s", $time, msg); \
// verilog_format: on

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  localparam MAX = 1000;
  integer cyc = 0;
  integer passed = 0;
  integer passed_until = 0;

  assert property (@(negedge clk) s_eventually 1)
    ++passed;

  // 'until' after 's_eventually' in the same module (#8614)
  assert property (@(negedge clk) cyc > 0 until cyc > 0)
    ++passed_until;

  // Attempts pend for up to nine cycles; each fires its own pass action
  integer passed_backlog = 0;
  assert property (@(negedge clk) s_eventually (cyc % 10 == 9))
    ++passed_backlog;

  integer passed_nested = 0;
  property p_sev_nine;
    s_eventually (cyc % 10 == 9);
  endproperty
  assert property (@(negedge clk) cyc > 0 |-> p_sev_nine)
    ++passed_nested;

  // A sequence antecedent
  integer passed_seq_ant = 0;
  assert property (@(negedge clk) (cyc % 10 == 1) ##1 (cyc % 10 == 2) |-> s_eventually (cyc % 10 == 5))
    ++passed_seq_ant;

  // Under `not`, every attempt still pending when the operand holds fails
  integer failed_not = 0;
  assert property (@(negedge clk) not s_eventually (cyc == 5))
  else ++failed_not;

  // A disable drops every pending attempt, not just the newest
  integer passed_disable = 0;
  assert property (@(negedge clk) disable iff (cyc % 10 == 4) s_eventually (cyc % 10 == 9))
    ++passed_disable;

  integer passed_disable_sampled = 0;
  assert property (@(negedge clk) disable iff ($sampled(cyc % 10 == 4)) s_eventually (cyc % 10 == 9))
    ++passed_disable_sampled;

  // A cover runs its pass action once per attempt as well
  integer covered_backlog = 0;
  cover property (@(negedge clk) s_eventually (cyc % 10 == 9)) ++covered_backlog;

  // An abort accounts each pending attempt once
  integer passed_accept = 0;
  assert property (@(negedge clk) accept_on (cyc % 10 == 4) s_eventually (cyc % 10 == 9))
    ++passed_accept;

  integer passed_reject = 0;
  integer failed_reject = 0;
  assert property (@(negedge clk) reject_on (cyc % 10 == 4) s_eventually (cyc % 10 == 9))
    ++passed_reject;
  else ++failed_reject;

  // A pass is not lost to a failure on the same tick
  integer passed_fby = 0;
  integer failed_fby = 0;
  wire fby_start = cyc % 10 == 2 || cyc % 10 == 3;
  assert property (@(negedge clk) fby_start #-# s_eventually (cyc % 10 == 5))
    ++passed_fby;
  else ++failed_fby;

  // In a task, with an end-of-simulation check
  integer failed_task = 0;
  task automatic check_task;
    assert property (@(negedge clk) s_eventually (cyc % 10 == 9))
    else ++failed_task;
  endtask
  initial check_task();

  // Under `not`, an obligation still pending at $finish is not a failure
  assert property (@(negedge clk) not ((cyc == 3) #=# s_eventually (cyc == 2 * MAX)));

  // A negated consequent fails when its operand holds on the antecedent's tick, and
  // never passes nonvacuously
  integer passed_not_imp = 0;
  integer failed_not_imp = 0;
  assert property (@(negedge clk) cyc == 3 |-> not s_eventually (cyc % 10 == 3))
    ++passed_not_imp;
  else ++failed_not_imp;

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $display("%d", passed);
      `checkd(passed, 999);
      `checkd(passed_until, 999);  // Same as 'passed': each attempt passes on its first edge
      `checkd(passed_backlog, 999);
      `checkd(passed_nested, 999);
      `checkd(passed_seq_ant, 999);
      `checkd(failed_not, 5);
      `checkd(passed_disable, 500);
      `checkd(passed_disable_sampled, 500);
      `checkd(covered_backlog, 999);
      `checkd(passed_accept, 999);
      `checkd(passed_reject, 500);
      `checkd(failed_reject, 499);
      `checkd(passed_fby, 200);
      `checkd(failed_fby, 799);
      `checkd(passed_not_imp, 998);
      `checkd(failed_not_imp, 1);
      `checkd(failed_task, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
