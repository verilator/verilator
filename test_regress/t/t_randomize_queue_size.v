// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   if (!bit'(cl.randomize())) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class Foo;
   rand int q[$];
   int      x = 1;
   constraint c {
      q.size() == 15;
   }
endclass

class Bar;
   rand int q[$];
   rand int min_size;
   rand int q2[$];
   constraint c {
      min_size > 2;
      q.size() >= min_size;
      q.size() < 10;
   };
   constraint c2 {
      q2.size() < 7;
   }
endclass

class Baz;
   rand Foo foo_arr[];
   constraint c_foo {
      foo_arr.size == 7;
   }
endclass

module t;
   initial begin
      Foo foo = new;
      Bar bar = new;
      Baz baz = new;

      void'(foo.randomize());
      if (foo.q.size() != 15) $stop;

      `check_rand(bar, bar.q.size(), bar.q.size() > 2 && bar.q.size() < 10);
      `check_rand(bar, bar.q2.size(), bar.q2.size() < 7);

      baz.foo_arr = new[4];
      for (int i = 0; i < 4; i++) baz.foo_arr[i] = new;
      baz.foo_arr[2].x = 2;
      void'(baz.randomize());

      if (baz.foo_arr.size() != 7) $stop;
      for (int i = 0; i < 4; i++)
        if (baz.foo_arr[i] == null) $stop;
      for (int i = 4; i < 7; i++)
        if (baz.foo_arr[i] != null) $stop;
      if (baz.foo_arr[2].x != 2) $stop;
      `check_rand(baz, baz.foo_arr[1].q[5], 1'b1);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
