// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Base;
   int value = 1;
   function void testBase;
      if (value != 1) $stop;
   endfunction
endclass

class Cls extends Base;
   function void testDerived;
      if (value != 1) $stop;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      c.testBase();
      c.testDerived();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
