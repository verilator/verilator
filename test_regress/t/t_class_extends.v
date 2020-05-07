// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Base0;
   // No members to check that to_string handles this
endclass

class Base1 extends Base0;
   int b1member;
endclass

class Base2 extends Base1;
   int b2member;
endclass

class Cls extends Base2;
   int imembera;
   int imemberb;
endclass : Cls

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      c.b1member = 10;
      c.b2member = 30;
      c.imembera = 100;
      c.imemberb = 110;
      $display("Display: set = \"%p\"", c);  // '{all 4 members}
      if (c.b1member != 10) $stop;
      if (c.b2member != 30) $stop;
      if (c.imembera != 100) $stop;
      if (c.imemberb != 110) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
