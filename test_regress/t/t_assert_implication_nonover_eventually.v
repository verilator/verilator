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
  logic a1 = 0, b1 = 0, c1 = 0, a2 = 0, b2 = 0;

  // a1 in cycle 3, c1 in cycle 4, b1 in cycle 6; a2 and b2 both only in cycle 9
  always @(posedge clk) begin
    cyc <= cyc + 1;
    a1 <= (cyc == 2);
    c1 <= (cyc == 3);
    b1 <= (cyc == 5);
    a2 <= (cyc == 8);
    b2 <= (cyc == 8);
    if (cyc == 16) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Single-cycle antecedent, b1 after it: every form passes once (pass actions run on
  // non-vacuous success) and nothing fails
  int pass_non = 0, pass_over = 0, pass_func = 0, pass_rose = 0;
  int fail_non = 0, fail_over = 0, fail_func = 0, fail_rose = 0;
  logic [2:0] h = 3'd3;
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
  // (it stays unresolved until the end of simulation, after the checks)
  int pass2_non = 0, pass2_over = 0, fail2_non = 0, fail2_over = 0;
  assert property (@(posedge clk) a2 |=> s_eventually b2) pass2_non = pass2_non + 1;
  else fail2_non = fail2_non + 1;
  assert property (@(posedge clk) a2 |-> s_eventually b2) pass2_over = pass2_over + 1;
  else fail2_over = fail2_over + 1;
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(pass2_non, 0);
      `checkd(pass2_over, 1);
      `checkd(fail2_non, 0);
      `checkd(fail2_over, 0);
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

  int cov_non = 0, cov_over = 0;
  cover property (@(posedge clk) a1 |=> s_eventually b1) cov_non = cov_non + 1;
  cover property (@(posedge clk) a1 |-> s_eventually b1) cov_over = cov_over + 1;
  always @(posedge clk)
    if (cyc == 15) begin
      `checkd(cov_non, 1);
      `checkd(cov_over, 1);
    end
endmodule
