// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   );

   class foo;
      int x = 1;
      function int get_x;
         return x;
      endfunction
      function int get_3;
         return 3;
      endfunction
   endclass

   typedef foo foo_t;

   class bar extends foo_t;
   endclass


   bar bar_foo_t_i;

   initial begin
      bar_foo_t_i = new;
      if (bar_foo_t_i.get_x() == 1 && bar_foo_t_i.get_3() == 3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $stop;
      end
   end
endmodule
