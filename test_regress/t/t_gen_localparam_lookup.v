// DESCRIPTION: Verilator: Self-checking test for localparams inside loop generate blocks
//
// This file ONLY is placed under the Creative Commons Public Domain Declaration,
// Version 1.0. See https://creativecommons.org
//
// SPDX-License-Identifier: CC0-1.0
// SPDX-FileCopyrightText: 2026 by Pragna Tummala

module t;
   for (genvar i = 0; i < 2; i++) begin : g
      localparam int DEP = 10 + i;
   end
   initial begin
      if (g.DEP != 10) $stop;
      if (g.DEP != 11) $stop;
      $write("*-* All Covered *-*\n");
      $finish;
   end
endmodule
