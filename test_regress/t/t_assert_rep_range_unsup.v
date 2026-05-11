// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk;
  bit a;
  bit b;

  property p_nc_range;
    @(posedge clk) a |-> b [= 1: 2];
  endproperty
  property p_nc_lhs_range;
    @(posedge clk) a [= 1: 2] |-> b;
  endproperty

  a_nc_range :
  assert property (p_nc_range);
  a_nc_lhs_range :
  assert property (p_nc_lhs_range);
endmodule
