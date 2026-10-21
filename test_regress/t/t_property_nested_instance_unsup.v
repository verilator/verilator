// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  bit a = 0;
  bit b = 0;

  property q_clk;
    @(posedge clk) b;
  endproperty

  property q_seq;
    b ##1 a;
  endproperty

  property q_rep;
    b [* 2];
  endproperty

  assert property (@(posedge clk) a |-> q_clk);
  assert property (@(posedge clk) a |-> q_seq);
  assert property (@(posedge clk) a |-> q_rep);

endmodule
