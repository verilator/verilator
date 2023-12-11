// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   int     array [10];
   logic   l;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         // Setup
         array[0] = 10;
         array[1] = 20;
         array[9] = 90;
      end
      else if (cyc < 99) begin
         l = (10 inside {array});
         if (l != 1) $stop;
         l = (20 inside {array});
         if (l != 1) $stop;
         l = (90 inside {array});
         if (l != 1) $stop;
         l = (99 inside {array});
         if (l != 0) $stop;
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
