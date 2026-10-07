// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Doha Nam
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input a
);
  // A cycle delay after 's_eventually' still requires default clocking (#8614)
  assert property (@(posedge clk) s_eventually a);
  always ##1;
endmodule
