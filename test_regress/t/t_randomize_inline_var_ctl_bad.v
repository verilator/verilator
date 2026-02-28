// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
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
      automatic Foo foo = new;
      automatic Foo qux = new;
      automatic Bar bar = new;
      automatic int x;
      void'(foo.randomize(x, foo.x, null, qux.x, bar.y, 0 + 1, x ** 2));
   end
endmodule
