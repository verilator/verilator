// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo #(type T=int);
   typedef Foo#(T) this_type;
   function int get_x;
      return T::get_s_x();
   endfunction
endclass

class Bar #(type S=int);
   typedef Bar #(S) this_type;
   typedef Foo#(this_type) foo_type;
   function int get_x;
      foo_type f = new;
      return f.get_x();
   endfunction
   static function int get_s_x;
      return S::x;
   endfunction
endclass

class Cls1;
   static int x = 1;
   typedef Bar#(Cls1) type_id;
endclass

class Cls2;
   static int x = 2;
   typedef Bar#(Cls2) type_id;
endclass

module t;
   initial begin
      Cls1::type_id bar1 = new;
      Cls2::type_id bar2 = new;

      if (bar1.get_x() != 1) $stop;
      if (bar2.get_x() != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
