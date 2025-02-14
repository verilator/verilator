// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Base;
   class Inner;
      int value = 10;
      function void testBaseInner;
         if (value != 10) $stop;
      endfunction
   endclass
   int value = 1;
   Inner inner = new;
   function void testBase;
      if (value != 1) $stop;
      if (inner.value != 10) $stop;
   endfunction
endclass

class Cls extends Base;
   function void testDerived;
      if (value != 1) $stop;
      if (inner.value != 10) $stop;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      c.testBase();
      c.testDerived();
      c.inner.testBaseInner();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
