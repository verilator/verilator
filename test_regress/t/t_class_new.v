// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class ClsNoArg;
   int imembera;
   function new();
      imembera = 5;
   endfunction
endclass

class ClsArg;
   int imembera;
   function new(int i);
      imembera = i + 1;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      ClsNoArg c1;
      ClsArg c2;
      c1 = new;
      if (c1.imembera != 5) $stop;
      c2 = new(2);
      if (c2.imembera != 3) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
