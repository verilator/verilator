// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input clk2,
    input a,
    input b
);

  // Property body already has its own @(posedge clk2); caller wraps another
  // @(posedge clk). Triggers "Clock event before property call and in its body"
  // unsupported path in inlineNamedProperty.
  property p;
    @(posedge clk2) a ##1 b;
  endproperty

  assert property (@(posedge clk) p);

endmodule
