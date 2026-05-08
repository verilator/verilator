// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Two V3AssertPre fallback paths for repetition ranges:
//   * [=M:N] nonconsec range -- NFA does not handle AstSNonConsRep yet
//   * [->M:N] under default clocking -- NFA bails when sensesp() is null
//     and the property inherits its clock from default clocking.

module t;
  bit clk;
  bit a;
  bit b;

  property p_nc_range;
    @(posedge clk) a |-> b [= 1: 2];
  endproperty

  a_nc_range :
  assert property (p_nc_range);
endmodule

module t_dc;
  bit clk;
  bit a;
  bit b;

  default clocking cb @(posedge clk);
  endclocking

  property p_goto_default_clock;
    a |-> b [-> 1: 2];
  endproperty

  a_goto_default_clock :
  assert property (p_goto_default_clock);
endmodule
