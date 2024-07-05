// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
   rand int zero;
   int two;
endclass

class Bar extends Foo;
   rand int one;
   static int three;

   function void test;
      logic[1:0] ok = '0;
      zero = 100;
      one = 200;
      two = 300;
      three = 400;
      for (int i = 0; i < 20; i++) begin
         void'(randomize(one));
         if (zero != 100) $stop;
         if (one != 200) ok[0] = 1;
         if (two != 300) $stop;
         if (three != 400) $stop;
      end
      if (!ok[0]) $stop;
      ok = '0;

      if (zero.rand_mode() != 1) $stop;
      if (one.rand_mode() != 1) $stop;
      zero = 500;
      one = 600;
      two = 700;
      three = 800;
      one.rand_mode(0);
      for (int i = 0; i < 20; i++) begin
         void'(randomize(one, two));
         if (zero != 500) $stop;
         if (one != 600) ok[0] = 1;
         if (two != 700) ok[1] = 1;
         if (three != 800) $stop;
      end
      if (one.rand_mode() != 0) $stop;
      one.rand_mode(1);
      if (ok != 'b11) $stop;
   endfunction
endclass

class Baz;
   int four;
   Bar bar;

   function new;
      bar = new;
   endfunction
endclass

class Qux;
   Baz baz;

   function new;
      baz = new;
   endfunction
endclass

class Boo extends Bar;
   rand int five;
endclass

module t;
   initial begin
      Boo boo = new;
      Bar bar = boo;
      Qux qux = new;
      logic[2:0] ok = '0;

      bar.test;

      bar.zero = 1000;
      bar.one = 2000;
      bar.two = 3000;
      bar.three = 4000;
      boo.five = 999999;
      for (int i = 0; i < 20; i++) begin
         int res = bar.randomize(two);
         if (boo.five != 999999) $stop;
      end

      bar.zero = 1000;
      bar.one = 2000;
      bar.two = 3000;
      bar.three = 4000;
      boo.five = 999999;
      for (int i = 0; i < 20; i++) begin
         int res = bar.randomize(two) with { two > 3000 && two < 4000; };
         if (bar.zero != 1000) $stop;
         if (bar.one != 2000) $stop;
         if (!(bar.two > 3000 && bar.two < 4000)) $stop;
         if (bar.three != 4000) $stop;
         if (boo.five != 999999) $stop;
      end

      qux.baz.bar.zero = 5000;
      qux.baz.bar.one = 6000;
      qux.baz.bar.two = 7000;
      qux.baz.bar.three = 8000;
      qux.baz.four = 9000;
      for (int i = 0; i < 20; i++) begin
         void'(qux.randomize(baz));
         if (qux.baz.bar.zero != 5000) $stop;
         if (qux.baz.bar.one != 6000) $stop;
         if (qux.baz.bar.two != 7000) $stop;
         if (qux.baz.bar.three != 8000) $stop;
         if (qux.baz.four != 9000) $stop;
      end
      for (int i = 0; i < 20; i++) begin
         void'(qux.randomize(baz.bar));
         if (qux.baz.bar.zero != 5000) ok[0] = 1;
         if (qux.baz.bar.one != 6000) ok[1] = 1;
         if (qux.baz.bar.two != 7000) $stop;
         if (qux.baz.bar.three != 8000) $stop;
         if (qux.baz.four != 9000) $stop;
      end
      if (!ok[0]) $stop;
      if (!ok[1]) $stop;
      ok = '0;
      qux.baz.bar.zero = 10000;
      qux.baz.bar.one = 20000;
      for (int i = 0; i < 20; i++) begin
         void'(qux.randomize(baz.four));
         if (qux.baz.bar.zero != 10000) $stop;
         if (qux.baz.bar.one != 20000) $stop;
         if (qux.baz.bar.two != 7000) $stop;
         if (qux.baz.bar.three != 8000) $stop;
         if (qux.baz.four != 9000) ok[0] = 1;
      end
      if (!ok[0]) $stop;
      ok = '0;
      qux.baz.four = 30000;
      for (int i = 0; i < 20; i++) begin
         void'(qux.randomize(baz.bar, qux.baz.bar.one, baz.four));
         if (qux.baz.bar.zero != 10000) ok[0] = 1;
         if (qux.baz.bar.one != 20000) ok[1] = 1;
         if (qux.baz.bar.two != 7000) $stop;
         if (qux.baz.bar.three != 8000) $stop;
         if (qux.baz.four != 30000) ok[2] = 1;
      end
      if (ok != 'b111) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
