// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc!=0) begin
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule
