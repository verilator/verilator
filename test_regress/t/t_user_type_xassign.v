// DESCRIPTION: Verilator: Demonstrate complex user typea problem with --x-assign
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   typedef logic [31:0] int_t;
   typedef int_t [6:0] bar_t;
   bar_t the_bar;

   logic [31:0] thing_one;
   always_comb begin
       for (int sel = 0; sel < 1; sel++)
           thing_one = the_bar[sel];
   end

   virtual class SomeClass;
       static function logic compare(int a, int b);
           return a > b;
       endfunction
   endclass

   logic [31:0] thing_two;
   always_comb begin
       for (int sel_a = 0; sel_a < 1; sel_a++)
           thing_two = the_bar[sel_a];
   end

   // finish report
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end


endmodule
