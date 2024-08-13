// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
   int x;

   function void test;
      int y;
      void'(randomize(y));
   endfunction
endclass

class Bar;
    int y;
endclass

module t;
   initial begin
      Foo foo = new;
      Foo qux = new;
      Bar bar = new;
      int x;
      void'(foo.randomize(x, foo.x, null, qux.x, bar.y, 0 + 1, x ** 2));
   end
endmodule
