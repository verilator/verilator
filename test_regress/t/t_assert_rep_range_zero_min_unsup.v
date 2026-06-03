// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Zero min count in a repetition range is IEEE-legal (16.9.2 / 16.9.2.1
// define an empty match for [*0]; the same applies to [->] and [=]) but
// V3AssertNfa cannot represent a 0-iteration goto/nonconsec match today,
// so V3Width emits E_UNSUPPORTED.

module t;
  bit clk;
  bit a;
  bit b;

  property p_goto_zero_min;
    @(posedge clk) a |-> b [-> 0: 2];
  endproperty
  property p_nc_zero_min;
    @(posedge clk) a |-> b [= 0: 2];
  endproperty

  a_goto_zero_min :
  assert property (p_goto_zero_min);
  a_nc_zero_min :
  assert property (p_nc_zero_min);
endmodule
