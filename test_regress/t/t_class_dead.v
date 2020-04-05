// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class EmptyClass_Dead;
endclass

module Mod_Dead;
class ModClass_Dead;
   int memberb_dead;
endclass
endmodule

//TODO dead check with class extends

module t (/*AUTOARG*/);

   generate
      if (0) begin
         Mod_Dead cell_dead();
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
