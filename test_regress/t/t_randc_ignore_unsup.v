// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   randc int i;

   function new;
      i = 0;
   endfunction

endclass

module t (/*AUTOARG*/);
   bit ok = 0;

   Cls obj;

   initial begin
      int rand_result;
      int prev_i;
      for (int i = 0; i < 10; i++) begin
         obj = new;
         rand_result = obj.randomize();
         if (i > 0 && obj.i != prev_i) begin
            ok = 1;
         end
         prev_i = obj.i;
      end
      if (ok) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else $stop;
   end
endmodule
