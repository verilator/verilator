// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Foo1;
   int x = 1;
   function int get_x;
      return x;
   endfunction
endclass

class Foo2;
   int x = 2;
   function int get_x;
      return x;
   endfunction
endclass

class Bar;
   typedef Foo1 foo_t;
   protected foo_t m_dict[int];

   function void set(int key);
      foo_t default_value = new;
      m_dict[key] = default_value;
   endfunction
   function foo_t get(int key);
      return m_dict[key];
   endfunction
endclass

class Baz #(type T=Foo1);
  protected T m_dict[int];

  function void set(int key);
     T default_value = new;
     m_dict[key] = default_value;
   endfunction
   function T get(int key);
      return m_dict[key];
   endfunction
endclass

class WBase;
endclass

class Wrapper#(type VAL_T=int);
   VAL_T value;
endclass

class Bum;
   typedef int map_t[string];
   map_t m_value;
   function new(map_t value);
      m_value = value;
   endfunction
endclass

module t;

   typedef WBase wrap_map_t[string];
   typedef WBase wrap_queue_t[$];

   localparam string str_key = "the_key";

   initial begin
      automatic Bar bar_i = new;
      automatic Baz baz_1_i = new;
      automatic Baz #(Foo2) baz_2_i = new;
      automatic Bum bum_i;

      automatic Wrapper#(wrap_map_t) wrap_map = new();
      automatic Wrapper#(wrap_queue_t) wrap_queue = new();

      bar_i.set(1);
      baz_1_i.set(2);
      baz_2_i.set(3);

      if (bar_i.get(1).get_x() != 1) $stop;
      if (baz_1_i.get(2).get_x() != 1) $stop;
      if (baz_2_i.get(3).get_x() != 2) $stop;

      bum_i = new('{str_key: 42});
      if (bum_i.m_value["the_key"] != 42) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
