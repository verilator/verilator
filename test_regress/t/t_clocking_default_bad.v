// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  clocking cb1 @(posedge clk);
  endclocking
  clocking cb2 @(negedge clk);
  endclocking

  default clocking cb1;
  default clocking cb2;
endmodule
