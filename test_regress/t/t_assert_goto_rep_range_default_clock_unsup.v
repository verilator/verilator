// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// A property that inherits its clock from `default clocking` has its
// sensitivity resolved only in V3AssertPre. V3AssertNfa bails early
// (propSpecp->sensesp() is null), so the [->M:N] range form lands in
// V3AssertPre's fallback and must emit a clean E_UNSUPPORTED.
module t;
  bit clk;
  bit a;
  bit b;

  default clocking cb @(posedge clk);
  endclocking

  property p;
    a |-> b [-> 1: 2];
  endproperty
  a1 :
  assert property (p);
endmodule
