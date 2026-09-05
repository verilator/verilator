// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`ifdef verilator
 `define no_optimize(v) $c(v)
`else
 `define no_optimize(v) (v)
`endif
// verilog_format: on

module t;
  logic clk = 0;
  int imm_fails = 0, conc_fails = 0;
  logic a = 1'b1;  // antecedent always true
  logic b = 1'b0;  // consequent always false -> assertion always violates

  always #5 clk = ~clk;

  // Immediate assertion: assertion_type SIMPLE_IMMEDIATE (mask value 2).
  always @(posedge clk)
    ia :
    assert (b)
    else imm_fails = imm_fails + 1;

  // Concurrent assertion: assertion_type CONCURRENT (mask value 1).
  ca :
  assert property (@(posedge clk) a |-> b)
  else conc_fails = conc_fails + 1;

  int ctl;

  // posedge clk at t = 5, 15, 25, 35, 45, 55, 65, 75, 85, 95.
  initial begin
    // Phase A (t=0..): everything on. edge@5 -> imm+1, conc+1.
    #6;  // t=6
    // Phase B: lock the on state, then $assertoff must be ignored while locked.
    $assertcontrol(1);  // Lock, all types
    $assertoff;  // ignored -> edges @15,@25 still fire both
    #24;  // t=30
    // Phase C: unlock, then turn off only SIMPLE_IMMEDIATE via assertion_type filter.
    $assertcontrol(2);  // Unlock
    $assertcontrol(4, 2);  // Off, assertion_type = SIMPLE_IMMEDIATE only
    #20;  // t=50: edges @35,@45 -> imm off, conc still on
    // Phase D: non-constant control_type and assertion_type re-enable the immediate.
    ctl = `no_optimize(3);  // On
    $assertcontrol(ctl, `no_optimize(2));  // non-const On, SIMPLE_IMMEDIATE
    #20;  // t=70: edges @55,@65 -> both on
    // Phase E: off everything, then a non-const action-control code (no runtime effect).
    $assertcontrol(4);  // Off all
    ctl = `no_optimize(7);  // Pass_Off (IEEE 1800-2023 Table 20-5 action control)
    $assertcontrol(ctl);  // non-const action-control: evaluated at runtime, ignored
    #30;  // t=100: edges @75,@85,@95 -> none
    $finish;
  end

  final begin
    `checkd(imm_fails, 5);
    `checkd(conc_fails, 7);  // Other sims: 7 or 1
    $write("*-* All Finished *-*\n");
  end
endmodule
