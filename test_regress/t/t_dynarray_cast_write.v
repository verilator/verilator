// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
   int x = 1;
endclass

class Bar extends Foo;
   function new;
      x = 2;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Bar bar = new;
      Foo foo = bar;
      Bar bars[] = new[1];
      $cast(bars[0], foo);

      if (bars[0].x != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
