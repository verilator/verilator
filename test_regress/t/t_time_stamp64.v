// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         $write("[%0t] In %m: Hi\n", $time);
         $printtimescale;
         $write("*-* All Finished *-*\n");
         $finish;
      end

   end
endmodule
