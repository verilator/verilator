// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   const int aconst = 10;
   static const int astatic = 20;
endclass

module t;
   initial begin
      Cls c = new;
      if (c.aconst !== 10) $stop;
      if (Cls::astatic !== 20) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
