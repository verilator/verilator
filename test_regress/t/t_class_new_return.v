// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );

   input clk;

   class foo;
      int a;
      function new;
         a = 1;
         return;
         a = 2;
      endfunction
      function int get_a;
         return a;
      endfunction
   endclass

   foo foo_i;
   initial foo_i = new;

   always @(posedge clk) begin
      if (foo_i.get_a() == 1) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else
        $stop;
   end
endmodule
