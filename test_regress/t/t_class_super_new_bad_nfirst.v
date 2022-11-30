// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
   int imemberb;
   function new(int adder);
      imemberb = 5 + adder;
   endfunction
endclass

class Cls extends Base;
   int imemberc;
   function new();
      imemberc = 10;
      super.new(imemberc);  // BAD not first
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls   c;
      c = new;
      if (c.imemberc != 10) $stop;
      if (c.imemberb != 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
