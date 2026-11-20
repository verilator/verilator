// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  wire a = cyc % 10 == 1;
  wire c = cyc % 10 == 4;

  // Test: each attempt passes once, vacuous attempts included
  int pass_bare = 0;
  int pass_nonoverlap = 0;
  int pass_seq_ant = 0;
  assert property (@(posedge clk) s_eventually c) ++pass_bare;
  assert property (@(posedge clk) a |=> s_eventually c) ++pass_nonoverlap;
  assert property (@(posedge clk) a ##1 cyc % 10 == 2 |-> s_eventually c) ++pass_seq_ant;

  // Test: the pass action runs on each vacuous success and once per nonvacuous success
  wire imp_a = cyc % 10 < 3;
  int pass_imp = 0;
  int fail_imp = 0;
  int pass_imp_nonoverlap = 0;
  int fail_imp_nonoverlap = 0;
  assert property (@(posedge clk) imp_a |-> s_eventually c) ++pass_imp;
  else ++fail_imp;
  assert property (@(posedge clk) imp_a |=> s_eventually c) ++pass_imp_nonoverlap;
  else ++fail_imp_nonoverlap;

  // Test: a disable drops an attempt waiting for its consequent, which then neither passes
  // nor fails, even at the end of simulation (IEEE 1800-2023 16.12)
  bit rst = 0;
  always @(negedge clk) rst <= cyc % 10 == 3;
  int pass_disable = 0;
  int fail_disable = 0;
  int pass_disable_never = 0;
  assert property (@(posedge clk) disable iff (rst) a |-> s_eventually (cyc % 10 == 5))
    ++pass_disable;
  else ++fail_disable;
  assert property (@(posedge clk) disable iff (rst) a |-> s_eventually (cyc > 1000))
    ++pass_disable_never;

  always @(posedge clk) ++cyc;

  always @(negedge clk) begin
    if (cyc == 95) begin
      `checkd(pass_bare, 95);
      `checkd(pass_nonoverlap, 95);
      `checkd(pass_seq_ant, 95);
      `checkd(pass_imp, 95);
      `checkd(fail_imp, 0);
      `checkd(pass_imp_nonoverlap, 95);
      `checkd(fail_imp_nonoverlap, 0);
      `checkd(pass_disable, 75);
      `checkd(fail_disable, 0);
      `checkd(pass_disable_never, 75);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
