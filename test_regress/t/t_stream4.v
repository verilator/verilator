// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Adrien Le Masle.
// SPDX-License-Identifier: CC0-1.0

//module t;
module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   logic [63:0] din;
   logic [63:0] dout;

   always_comb begin
      dout = {<<8{din}};
   end

   always @(posedge clk) begin
      if (cyc != 0) begin
         cyc <= cyc + 1;

         if (cyc == 1) begin
            din <= 64'h1122334455667788;
         end

         if (cyc == 2) begin
            if (dout != 64'h8877665544332211) $stop;
         end

         if (cyc == 3) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
