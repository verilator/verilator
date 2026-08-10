// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  bit a;
  bit b;
  bit c;
  bit d;

  // verilog_format: off
  assert property (@(posedge clk) (a ##1 b) and (c ##1 d));

  assert property (@(posedge clk) (a |-> b) and (c |-> d));
  // verilog_format: on

endmodule
