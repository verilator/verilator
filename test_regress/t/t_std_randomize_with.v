// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      int a, b;
      // if (std::randomize(a, b) != 1) $stop;
      if (std::randomize(a, b) with { 2 < a; a < 7; b < a; } != 1) $stop;
      if (!(2 < a && a < 7 && b < a)) $stop;
      $write("-*-* All Finished *-*-\n");
      $finish;
   end
endmodule
