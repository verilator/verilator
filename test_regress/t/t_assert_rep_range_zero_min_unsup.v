// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk;
  bit a;
  bit b;

  // Zero min count in a repetition range is parser-legal but maps to a
  // zero-count repetition that V3AssertNfa cannot represent today.
  // Both forms emit E_UNSUPPORTED with an IEEE 1800-2023 16.9.2 anchor.
  property p_goto_zero_min;
    @(posedge clk) a |-> b [-> 0: 2];
  endproperty
  property p_nc_zero_min;
    @(posedge clk) a |-> b [= 0: 2];
  endproperty

  a1 :
  assert property (p_goto_zero_min);
  a2 :
  assert property (p_nc_zero_min);

endmodule
