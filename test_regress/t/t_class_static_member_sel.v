// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
   static int x = 1;
endclass

class Bar;
   Foo f;
   function new;
      f = new;
   endfunction
endclass

class Baz;
   function static Bar get_bar;
      Bar b = new;
      return b;
   endfunction
endclass

module t (/*AUTOARG*/
   );

   initial begin
      Foo foo = new;
      Bar bar = new;
      Baz baz = new;

      if (foo.x != 1) $stop;

      foo.x = 2;
      if (foo.x != 2) $stop;

      bar.f.x = 3;
      if (bar.f.x != 3) $stop;

      baz.get_bar().f.x = 4;
      if (baz.get_bar().f.x != 4) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
