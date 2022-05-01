// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   reg [43:0]   mi;
   wire [31:0]  mo;
   muxtop um ( mi, mo);

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            mi <= 44'h1234567890;
         end
         if (cyc==3) begin
            if (mo !== 32'h12345678) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module muxtop (
   input [ 43:0 ] i,
   output reg [ 31:0 ] o
   );

   always @ ( i[43:0] )  // Verify we ignore ranges on always statement sense lists
     o = MUX( i[39:0] );

   function [31:0] MUX;
      input [39:0] XX ;
      begin
         MUX = XX[39:8];
      end
   endfunction
endmodule
