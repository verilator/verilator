// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk;
  bit a;
  bit b;

  // Range form of [=M:N] nonconsecutive repetition is not yet supported
  // by V3AssertNfa or V3AssertPre; parser accepts it and V3AssertPre emits
  // a clean E_UNSUPPORTED.
  property p;
    @(posedge clk) a |-> b [= 1: 2];
  endproperty
  a_p :
  assert property (p);

endmodule
