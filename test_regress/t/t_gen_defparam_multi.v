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
   parameter PAR = 3;

   defparam PAR = 5;

   wire [31:0] o2a, o2b, o3a, o3b;

   m1 #(0) m1a(.o2(o2a), .o3(o3a));
   m1 #(1) m1b(.o2(o2b), .o3(o3b));

   always @ (posedge clk) begin
      if (PAR != 5) $stop;
      if (o2a != 8) $stop;
      if (o2b != 4) $stop;
      if (o3a != 80) $stop;
      if (o3b != 40) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module m1 (output wire [31:0] o2,
           output wire [31:0] o3);
   parameter W = 0;
   generate
      if (W == 0) begin
         m2 m2 (.*);
         defparam m2.PAR2 = 8;
         defparam m2.m3.PAR3 = 80;
      end
      else begin
         m2 m2 (.*);
         defparam m2.PAR2 = 4;
         defparam m2.m3.PAR3 = 40;
      end
   endgenerate
endmodule

module m2 (output wire [31:0] o2,
           output wire [31:0] o3);
   parameter PAR2 = 20;
   assign o2 = PAR2;
   m3 m3 (.*);
endmodule

module m3 (output wire [31:0] o3);
   parameter PAR3 = 40;
   assign o3 = PAR3;
endmodule
