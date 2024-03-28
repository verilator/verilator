// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Rnd;
   rand bit x;
endclass

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   Rnd c;

   input clk;

   integer cyc;
   integer rand_result;
   integer seed = 123;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc != 0) begin
         if (cyc == 10) begin
            #5;
            $display("dist: %f ", $dist_poisson(seed, 12));  // Get verilated_probdist.cpp
            c = new;
            rand_result = c.randomize();
            $display("rand: %x x: %x ", rand_result, c.x);  // Get verilated_random.cpp
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

   cyc_eq_5: cover property (@(posedge clk) cyc==5) $display("*COVER: Cyc==5");

   export "DPI-C" function dpix_f_int;
   function int dpix_f_int ();
      return cyc;
   endfunction
endmodule
