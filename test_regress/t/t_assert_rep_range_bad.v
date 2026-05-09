// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk;
  bit a;
  bit b;
  int n;

  // Goto non-constant max bound.
  property p_goto_nonconst;
    @(posedge clk) a |-> b [-> 1: n];
  endproperty
  // Nonconsecutive non-constant max bound.
  property p_nc_nonconst;
    @(posedge clk) a |-> b [= 1: n];
  endproperty
  // Goto non-constant min bound.
  property p_goto_min_nonconst;
    @(posedge clk) a |-> b [-> n: 2];
  endproperty
  // Nonconsecutive non-constant min bound.
  property p_nc_min_nonconst;
    @(posedge clk) a |-> b [= n: 2];
  endproperty
  // Goto max < min.
  property p_goto_bad_order;
    @(posedge clk) a |-> b [-> 3: 1];
  endproperty
  // Nonconsecutive max < min.
  property p_nc_bad_order;
    @(posedge clk) a |-> b [= 3: 1];
  endproperty
  // Goto min < 0 is a hard error.
  property p_goto_neg_min;
    @(posedge clk) a |-> b [-> -1: 2];
  endproperty
  // Nonconsecutive min < 0 is a hard error.
  property p_nc_neg_min;
    @(posedge clk) a |-> b [= -1: 2];
  endproperty

  a1 :
  assert property (p_goto_nonconst);
  a2 :
  assert property (p_nc_nonconst);
  a3 :
  assert property (p_goto_min_nonconst);
  a4 :
  assert property (p_nc_min_nonconst);
  a5 :
  assert property (p_goto_bad_order);
  a6 :
  assert property (p_nc_bad_order);
  a7 :
  assert property (p_goto_neg_min);
  a8 :
  assert property (p_nc_neg_min);

endmodule
