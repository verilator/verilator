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
  bit rst = 0;

  property q_dis;
    disable iff (rst) b;
  endproperty

  assert property (@(posedge clk) a |-> q_dis);

endmodule
