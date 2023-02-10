// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   );

   class Foo;
      int x = 1;
      function int get_x;
         return x;
      endfunction
      function int get_3;
         return 3;
      endfunction
   endclass

   class Bar #(type T=Foo) extends T;
   endclass

   class Baz;
      int x = 2;
      function int get_x;
         return x;
      endfunction
      function int get_4;
         return 4;
      endfunction
   endclass

   class ExtendBar extends Bar;
     function int get_x;
        return super.get_x();
     endfunction
     function int get_6;
        return 2 * get_3();
     endfunction
   endclass

   Bar bar_foo_i;
   Bar #(Baz) bar_baz_i;
   ExtendBar extend_bar_i;

   initial begin
      bar_foo_i = new;
      bar_baz_i = new;
      extend_bar_i = new;
      if (bar_foo_i.get_x() == 1 && bar_foo_i.get_3() == 3 &&
          bar_baz_i.get_x() == 2 && bar_baz_i.get_4() == 4 &&
          extend_bar_i.get_x() == 1 && extend_bar_i.get_6() == 6) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $stop;
      end
   end
endmodule
