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
   integer cyc; initial cyc=0;

   reg [7:0] crc;
   reg [2:0] sum;
   wire [2:0] in = crc[2:0];
   wire [2:0] out;

   MxN_pipeline pipe (in, out, clk);

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%b sum=%x\n",$time, cyc, crc, sum);
      cyc <= cyc + 1;
      crc <= {crc[6:0], ~^ {crc[7],crc[5],crc[4],crc[3]}};
      if (cyc==0) begin
	 // Setup
	 crc <= 8'hed;
	 sum <= 3'h0;
      end
      else if (cyc>10 && cyc<90) begin
	 sum <= {sum[1:0],sum[2]} ^ out;
      end
      else if (cyc==99) begin
	 if (crc !== 8'b01110000) $stop;
	 if (sum !== 3'h3) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module dffn (q,d,clk);
   parameter BITS = 1;

   input [BITS-1:0]  d;
   output reg [BITS-1:0] q;
   input 	     clk;

   always @ (posedge clk) begin
      q <= d;
   end

endmodule

module MxN_pipeline (in, out, clk);
   parameter M=3, N=4;

   input [M-1:0] in;
   output [M-1:0] out;
   input 	  clk;

   // Unsupported: Per-bit array instantiations with output connections to non-wires.
   //wire [M*(N-1):1] t;
   //dffn #(M) p[N:1] ({out,t},{t,in},clk);

   wire [M*(N-1):1] w;
   wire [M*N:1] q;
   dffn #(M) p[N:1] (q,{w,in},clk);
   assign 	{out,w} = q;

endmodule
