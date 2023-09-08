// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
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

module t (/*AUTOARG*/
   );

   initial begin
      Bar bar_i = new;
      Baz baz_1_i = new;
      Baz #(Foo2) baz_2_i = new;

      bar_i.set(1);
      baz_1_i.set(2);
      baz_2_i.set(3);

      if (bar_i.get(1).get_x() == 1 &&
          baz_1_i.get(2).get_x() == 1 &&
          baz_2_i.get(3).get_x() == 2) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $stop;
      end
   end
endmodule
