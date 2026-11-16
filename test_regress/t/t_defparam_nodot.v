// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  parameter PAR = 3;
  defparam PAR = 5;

  parameter PAR1 = 10;
  parameter PAR2 = 20;
  defparam PAR1 = 1, PAR2 = 2;

  initial begin
    if (PAR != 5) $stop;
    if (PAR1 != 1) $stop;
    if (PAR2 != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
