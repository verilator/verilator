// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Cls;
   int imembera;
   int imemberb;
endclass : Cls

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      if (c != null) $stop;
      $display("Display: null = \"%p\"", c);  // null
      c = new;
      $display("Display: newed = \"%p\"", c);  // '{imembera:0, imemberb:0}
      c.imembera = 10;
      c.imemberb = 20;
      $display("Display: set = \"%p\"", c);  // '{imembera:10, imemberb:20}
      if (c.imembera != 10) $stop;
      if (c.imemberb != 20) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
