// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aisha Salimgereyeva
// SPDX-License-Identifier: CC0-1.0

module t (
    input wire clk
);

  // Clocking block declared before the drivers it contends with, so the
  // conflict is found on reaching the design driver.
  logic early_assign;
  logic early_always;

  clocking cb_early @(posedge clk);
    output early_assign;
    output early_always;
  endclocking

  assign early_assign = 1'b1;
  always @(posedge clk) early_always <= 1'b1;

  // Continuous assignment against a clocking block output: an unambiguous
  // driver conflict, reported by MULTIDRIVEN.
  logic late_assign;
  assign late_assign = 1'b1;

  // Plain always block against a clocking block output: a deliberate testbench
  // idiom, so reported only by the off-by-default MULTIDRIVENPROC.
  logic late_always;
  always @(posedge clk) late_always <= 1'b1;

  // Driven by two clocking blocks, reported by MULTIDRIVEN.
  logic dual_clocking;

  // Driven only by a clocking block: legal, must not warn.
  logic clocking_only;

  // Read by a clocking block rather than driven: legal, must not warn.
  logic observed;
  always_ff @(posedge clk) observed <= ~observed;

  clocking cb_late @(posedge clk);
    output late_assign;
    output late_always;
    output dual_clocking;
    output clocking_only;
    input observed;
  endclocking

  clocking cb_dual @(posedge clk);
    output dual_clocking;
  endclocking

  // Declaration initializer alongside a clocking block output: the initializer
  // is not a competing driver, must not warn.
  logic decl_init = 1'b0;

  // One signal named by two clockvars of the same clocking block: still a
  // single driver, must not warn.
  logic aliased;

  clocking cb_alias @(posedge clk);
    output decl_init;
    output cv_a = aliased;
    output cv_b = aliased;
  endclocking

endmodule
