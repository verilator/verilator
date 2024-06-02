// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            // New number format
            if ('0 !== {66{1'b0}}) $stop;
            if ('1 !== {66{1'b1}}) $stop;
            if ('x !== {66{1'bx}}) $stop;
            if ('z !== {66{1'bz}}) $stop;
`ifndef NC      // NC-Verilog 5.50-s09 chokes on this test
            if ("\v" != 8'd11) $stop;
            if ("\f" != 8'd12) $stop;
            if ("\a" != 8'd7) $stop;
            if ("\x9a" != 8'h9a) $stop;
            if ("\xf1" != 8'hf1) $stop;
`endif
         end
         if (cyc==8) begin
         end
         if (cyc==9) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
