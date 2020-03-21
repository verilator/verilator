// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2015 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;
   parameter ONE = 1;

   wire [17:10] bitout;
   reg  [7:0] allbits;
   reg  [15:0] onebit;

   sub #(1)
     sub0 (allbits, onebit[1:0], bitout[10]),
     sub1 (allbits, onebit[3:2], bitout[11]),
     sub2 (allbits, onebit[5:4], bitout[12]),
     sub3 (allbits, onebit[7:6], bitout[13]),
     sub4 (allbits, onebit[9:8], bitout[14]),
     sub5 (allbits, onebit[11:10], bitout[15]),
     sub6 (allbits, onebit[13:12], bitout[16]),
     sub7 (allbits, onebit[15:14], bitout[17]);

   integer     x;

   always @ (posedge clk) begin
      //$write("%x\n", bitout);
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    allbits <= 8'hac;
	    onebit <= 16'hc01a;
	 end
	 if (cyc==2) begin
	    if (bitout !== 8'h07) $stop;
	    allbits <= 8'hca;
	    onebit <= 16'h1f01;
	 end
	 if (cyc==3) begin
	    if (bitout !== 8'h41) $stop;
	    if (sub0.bitout !== 1'b1) $stop;
	    if (sub1.bitout !== 1'b0) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule

`ifdef USE_INLINE
 `define INLINE_MODULE /*verilator inline_module*/
`else
 `define INLINE_MODULE /*verilator public_module*/
`endif

module sub (input [7:0] allbits, input [1:0] onebit, output bitout);
   `INLINE_MODULE
     parameter integer P = 0;
   initial if (P != 1) $stop;
   assign bitout = (^ onebit) ^ (^ allbits);
endmodule
