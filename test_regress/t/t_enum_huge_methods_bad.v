// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   typedef enum logic [159:0] {
        E01 = 160'h1,
        ELARGE = 160'h1234_4567_abcd_1234_4567_abcd
         } my_t;

   my_t e;

   int    cyc;

   // Check runtime
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
         // Setup
         e <= E01;
      end
      else if (cyc==1) begin
         $display(e.name);
         e <= ELARGE;
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
