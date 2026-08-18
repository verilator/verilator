// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a = 1'b1;

  property p_default_2005;
    @(posedge clk) a ##1 a;
  endproperty

  assert property (p_default_2005);
endmodule
