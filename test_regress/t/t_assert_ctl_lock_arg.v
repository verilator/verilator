// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Run with +verilator+assert+lock, which freezes the enabled assertions, so
// every assertion control below is ignored and all directives keep firing.

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
// verilog_format: on

`ifdef T_ASSERT_CTL_LOCK_ARG_NOASSERT
`define ctl_on_off 3  // On, ignored as the assertions stay disabled
`define expected 0
`else
`define ctl_on_off 4  // Off, ignored as the assertions stay enabled
`define expected 10
`endif

module t;
  logic clk = 0;
  logic fals = 1'b0;

  int imm_fails = 0;
  int conc_fails = 0;
  int assume_fails = 0;
  int ctl;

  always #5 clk = ~clk;

  // posedge clk at t = 5, 15, 25, 35, 45, 55, 65, 75, 85, 95
  always @(posedge clk) imm_assert : assert (fals) else imm_fails = imm_fails + 1;

  conc_assert : assert property (@(posedge clk) fals) else conc_fails = conc_fails + 1;

  conc_assume : assume property (@(posedge clk) fals) else assume_fails = assume_fails + 1;

  initial begin
    #6;  // t=6
    $assertcontrol(`ctl_on_off);  // On or Off, whichever would flip all types
    #10;  // t=16
    $assertcontrol(`ctl_on_off, 2);  // Same, but only for SIMPLE_IMMEDIATE
    #10;  // t=26
    $assertcontrol(1);  // Lock
    $assertcontrol(2);  // Unlock
    #10;  // t=36
    $assertcontrol(5);  // Kill
    #10;  // t=46
    $assertpassoff;
    $assertfailoff;
    #10;  // t=56
    ctl = `ctl_on_off;
    $assertcontrol(ctl);  // Same again, via a non-constant control_type
    #10;  // t=66
    $assertkill;
    #34;  // t=100
    $finish;
  end

  // Every directive kept the enabled state it started with, as no control
  // above took effect
  final begin
    `checkd(imm_fails, `expected);
    `checkd(conc_fails, `expected);
    `checkd(assume_fails, `expected);
    $write("*-* All Finished *-*\n");
  end
endmodule
