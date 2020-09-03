// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc; initial cyc = 0;
   integer a;
   integer b;

   initial begin
      a <= 22;
      b <= 33;
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==99) begin
         if (a != 22) $stop;
         if (b != 33) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
