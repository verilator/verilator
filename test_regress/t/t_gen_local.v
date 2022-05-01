// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer      cyc = 0;

   localparam N = 31;

   wire [31:0]  vec;

   generate
      genvar  g;  // bug461
      begin : topgen
         for (g=0; g<N; ++g) begin : gfor
            assign vec[g] = (g<2);
         end
      end
   endgenerate

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 3) begin
         if (vec != 32'b0011) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
