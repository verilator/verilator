// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg signed i;
   wire signed o1;
   wire signed o2;

   integer cyc; initial cyc = 0;

   sub1 sub1 (.i(i), .o(o1));
   sub2 sub2 (.i(o1), .o(o2));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
         i <= 1'b0;
      end
      else if (cyc==1) begin
         if (o2 != 1'b0) $stop;
         i <= 1'b1;
      end
      else if (cyc==2) begin
         if (o2 != 1'b1) $stop;
      end
      if (cyc==3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

//msg2540
module sub1 (
             input signed  i,
             output wire signed o);
   assign o = ~i;
endmodule

module sub2 (i,o);
   input signed  i;
   output signed o;
   wire signed o = ~i;
endmodule
