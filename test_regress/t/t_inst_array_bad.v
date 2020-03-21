// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   wire [7:0] bitout;
   reg  [7:0] allbits;
   reg  [7:0]  onebit;
   reg  [8:0] onebitbad;  // Wrongly sized

   sub sub [7:0] (allbits, onebitbad, bitout);

   // This is ok.
   wire [9:8] b;
   wire [1:0] c;
   sub sub2 [9:8] (allbits,b,c);

endmodule

module sub (input [7:0] allbits, input onebit, output bitout);
   assign bitout = onebit ^ (^ allbits);
endmodule
