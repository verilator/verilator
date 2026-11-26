// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off DECLFILENAME
module t (
    input clk
);

  bit a = 0;
  bit b = 0;
  bit c = 0;

  property q_clk;
    @(posedge clk) b;
  endproperty

  property q_seq;
    b ##1 a;
  endproperty

  property q_rep;
    b [* 2];
  endproperty

  property q_arg(x);
    x ##1 x;
  endproperty

  property q_chain(x);
    q_arg(x);
  endproperty

  assert property (@(posedge clk) a |-> q_clk);
  assert property (@(posedge clk) a |-> q_seq);
  assert property (@(posedge clk) a |-> q_rep);
  // Reported at the nested instance also in a composite or through a chain, and 'c' that
  // only the rejected instance reads is not reported as unused
  assert property (@(posedge clk) q_seq or a);
  assert property (@(posedge clk) a |-> q_chain(c));

endmodule
