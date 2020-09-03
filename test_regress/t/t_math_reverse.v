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
   integer cyc; initial cyc=1;

   reg [7:0] crc;

   // Build up assignments
   wire [7:0] bitrev;
   assign     bitrev[7] = crc[0];
   assign     bitrev[6] = crc[1];
   assign     bitrev[5] = crc[2];
   assign     bitrev[4] = crc[3];
   assign     bitrev[0] = crc[7];
   assign     bitrev[1] = crc[6];
   assign     bitrev[2] = crc[5];
   assign     bitrev[3] = crc[4];

   // Build up always assignments
   reg [7:0] bitrevb;
   always @ (/*AS*/crc) begin
      bitrevb[7] = crc[0];
      bitrevb[6] = crc[1];
      bitrevb[5] = crc[2];
      bitrevb[4] = crc[3];
      bitrevb[0] = crc[7];
      bitrevb[1] = crc[6];
      bitrevb[2] = crc[5];
      bitrevb[3] = crc[4];
   end

   // Build up always assignments
   reg [7:0] bitrevr;
   always @ (posedge clk) begin
      bitrevr[7] <= crc[0];
      bitrevr[6] <= crc[1];
      bitrevr[5] <= crc[2];
      bitrevr[4] <= crc[3];
      bitrevr[0] <= crc[7];
      bitrevr[1] <= crc[6];
      bitrevr[2] <= crc[5];
      bitrevr[3] <= crc[4];
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc<=cyc+1;
	 //$write("cyc=%0d crc=%x r=%x\n", cyc, crc, bitrev);
	 crc <= {crc[6:0], ~^ {crc[7],crc[5],crc[4],crc[3]}};
	 if (cyc==1) begin
	    crc <= 8'hed;
	 end
	 if (cyc==2 && bitrev!=8'hb7) $stop;
	 if (cyc==3 && bitrev!=8'h5b) $stop;
	 if (cyc==4 && bitrev!=8'h2d) $stop;
	 if (cyc==5 && bitrev!=8'h16) $stop;
	 if (cyc==6 && bitrev!=8'h8b) $stop;
	 if (cyc==7 && bitrev!=8'hc5) $stop;
	 if (cyc==8 && bitrev!=8'he2) $stop;
	 if (cyc==9 && bitrev!=8'hf1) $stop;
	 if (bitrevb != bitrev) $stop;
	 if (cyc==3 && bitrevr!=8'hb7) $stop;
	 if (cyc==4 && bitrevr!=8'h5b) $stop;
	 if (cyc==5 && bitrevr!=8'h2d) $stop;
	 if (cyc==6 && bitrevr!=8'h16) $stop;
	 if (cyc==7 && bitrevr!=8'h8b) $stop;
	 if (cyc==8 && bitrevr!=8'hc5) $stop;
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
