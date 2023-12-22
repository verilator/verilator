// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module Mod_Dead;
endmodule

module t (/*AUTOARG*/);

   Mod_Dead cell_keptdead();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
