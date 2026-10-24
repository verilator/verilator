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
  logic a1 = 0, b1 = 0, c1 = 0, a2 = 0, b2 = 0, a3 = 0, b3 = 0;
  logic [2:0] h = 3'd0;

  // a1 in cycle 3, c1 in cycle 4, b1 in cycle 6; a2 and b2 both only in cycle 9;
  // a3 in cycles 11 and 12, b3 in cycle 13; h is 3 from cycle 1
  always @(posedge clk) begin
    cyc <= cyc + 1;
    a1 <= (cyc == 2);
    c1 <= (cyc == 3);
    b1 <= (cyc == 5);
    a2 <= (cyc == 8);
    b2 <= (cyc == 8);
    a3 <= (cyc == 10 || cyc == 11);
    b3 <= (cyc == 12);
    h <= 3'd3;
    if (cyc == 16) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Single-cycle antecedent, b1 after it: every form passes once (pass actions run on
  // non-vacuous success) and nothing fails
  int pass_non = 0, pass_over = 0, pass_func = 0, pass_rose = 0;
  int fail_non = 0, fail_over = 0, fail_func = 0, fail_rose = 0;
  function automatic int burst_len(logic [2:0] hb);
    return (hb == 3'd3) ? 4 : 1;
  endfunction
  assert property (@(posedge clk) a1 |=> s_eventually b1) pass_non = pass_non + 1;
  else fail_non = fail_non + 1;
  assert property (@(posedge clk) a1 |-> s_eventually b1) pass_over = pass_over + 1;
  else fail_over = fail_over + 1;
  assert property (@(posedge clk) (a1 && burst_len(h) > 1) |=> s_eventually b1)
    pass_func = pass_func + 1;
  else fail_func = fail_func + 1;
  assert property (@(posedge clk) $rose(a1) |=> s_eventually b1) pass_rose = pass_rose + 1;
  else fail_rose = fail_rose + 1;
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(pass_non, 1);
      `checkd(pass_over, 1);
      `checkd(pass_func, 1);
      `checkd(pass_rose, 1);
      `checkd(fail_non, 0);
      `checkd(fail_over, 0);
      `checkd(fail_func, 0);
      `checkd(fail_rose, 0);
    end

  // b2 only in a2's own cycle: |-> passes, |=> starts one cycle later and never passes
  // (it stays unresolved until the end of simulation, after the checks, and then fails
  // once: the .py checks the message)
  int pass2_non = 0, pass2_over = 0, fail2_non = 0, fail2_over = 0;
  assert property (@(posedge clk) a2 |=> s_eventually b2) pass2_non = pass2_non + 1;
  else begin
    fail2_non = fail2_non + 1;
    $write("fail2_non=%0d at the end of simulation\n", fail2_non);
  end
  assert property (@(posedge clk) a2 |-> s_eventually b2) pass2_over = pass2_over + 1;
  else fail2_over = fail2_over + 1;
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(pass2_non, 0);
      `checkd(pass2_over, 1);
      `checkd(fail2_non, 0);
      `checkd(fail2_over, 0);
    end

  // Two attempts wait at the same time (from a3 in cycles 11 and 12) and both pass on b3
  int pass3_non = 0, fail3_non = 0;
  assert property (@(posedge clk) a3 |=> s_eventually b3) pass3_non = pass3_non + 1;
  else fail3_non = fail3_non + 1;
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(pass3_non, 2);
      `checkd(fail3_non, 0);
    end

  // |=> then |->: c1 is true one cycle after a1, so the chain passes once; with the
  // operands swapped a1 is never one cycle after c1 and the chain is vacuous
  int pass_chain = 0, pass_chain0 = 0, fail_chain = 0, fail_chain0 = 0;
  assert property (@(posedge clk) a1 |=> c1 |-> s_eventually b1) pass_chain = pass_chain + 1;
  else fail_chain = fail_chain + 1;
  assert property (@(posedge clk) c1 |=> a1 |-> s_eventually b1) pass_chain0 = pass_chain0 + 1;
  else fail_chain0 = fail_chain0 + 1;
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(pass_chain, 1);
      `checkd(pass_chain0, 0);
      `checkd(fail_chain, 0);
      `checkd(fail_chain0, 0);
    end

  // Procedural assertions, clocked by their always block, stay on V3AssertPre
  int pass_proc = 0, pass_proc_rep = 0, fail_proc = 0, fail_proc_rep = 0;
  always @(posedge clk) begin
    assert property (a1 |=> s_eventually b1) pass_proc = pass_proc + 1;
    else fail_proc = fail_proc + 1;
    assert property (a1 [* 1] |=> s_eventually b1) pass_proc_rep = pass_proc_rep + 1;
    else fail_proc_rep = fail_proc_rep + 1;
  end
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(pass_proc, 1);
      `checkd(pass_proc_rep, 1);
      `checkd(fail_proc, 0);
      `checkd(fail_proc_rep, 0);
    end

  sub_default_disable sub (
      .clk(clk),
      .cyc(cyc),
      .a1(a1),
      .b1(b1)
  );

  int cov_non = 0, cov_over = 0;
  cover property (@(posedge clk) a1 |=> s_eventually b1) cov_non = cov_non + 1;
  cover property (@(posedge clk) a1 |-> s_eventually b1) cov_over = cov_over + 1;
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(cov_non, 1);
      `checkd(cov_over, 1);
    end
endmodule

// A procedural assertion under a default disable iff stays on V3AssertPre. rst stays low:
// V3AssertPre applies disable iff only when an attempt starts, not while s_eventually waits
module sub_default_disable (
    input clk,
    input int cyc,
    input logic a1,
    input logic b1
);
  logic rst = 0;
  default disable iff (rst);
  int pass_proc = 0, fail_proc = 0;
  always @(posedge clk) begin
    assert property (a1 |=> s_eventually b1) pass_proc = pass_proc + 1;
    else fail_proc = fail_proc + 1;
  end
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(pass_proc, 1);
      `checkd(fail_proc, 0);
    end
endmodule
