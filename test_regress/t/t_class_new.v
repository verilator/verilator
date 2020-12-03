// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class ClsNoArg;
   const int imembera;  // Ok for new() to assign to a const
   function new();
      imembera = 5;
   endfunction : new
endclass

class ClsArg;
   int imembera;
   function new(int i);
      imembera = i + 1;
   endfunction
   function int geta;
      return imembera;
   endfunction
   static function ClsArg create6;
      ClsArg obj;
      obj = new(6 - 1);
      return obj;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      ClsNoArg c1;
      ClsArg c2;

      c1 = new;
      if (c1.imembera != 5) $stop;

      c2 = new(3 - 1);
      if (c2.imembera != 3) $stop;
      if (c2.geta() != 3) $stop;

      c2 = ClsArg::create6();
      if (c2.imembera != 6) $stop;
      if (c2.geta() != 6) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
