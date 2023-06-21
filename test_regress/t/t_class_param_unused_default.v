// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Bar#(type T = int);
   T t;
   function new;
      t = new;
   endfunction
endclass

class Baz;
   int x = 1;
endclass

module t (/*AUTOARG*/);
   initial begin
      Bar#(Baz) bar_baz = new;
      if (bar_baz.t.x != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
