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

   integer cyc; initial cyc=0;
   reg [63:0] crc;
   reg [31:0] sum;

   wire [15:0]		out0;
   wire [15:0]		out1;
   wire [15:0] 		inData = crc[15:0];
   wire  		wr0a = crc[16];
   wire  		wr0b = crc[17];
   wire  		wr1a = crc[18];
   wire  		wr1b = crc[19];

   fifo fifo (
	      // Outputs
	      .out0			(out0[15:0]),
	      .out1			(out1[15:0]),
	      // Inputs
	      .clk			(clk),
	      .wr0a			(wr0a),
	      .wr0b			(wr0b),
	      .wr1a			(wr1a),
	      .wr1b			(wr1b),
	      .inData			(inData[15:0]));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%x q=%x\n",$time, cyc, crc, sum);
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 sum <= 32'h0;
      end
      else if (cyc>10 && cyc<90) begin
	 sum <= {sum[30:0],sum[31]} ^ {out1, out0};
      end
      else if (cyc==99) begin
	 if (sum !== 32'he8bbd130) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module fifo (/*AUTOARG*/
   // Outputs
   out0, out1,
   // Inputs
   clk, wr0a, wr0b, wr1a, wr1b, inData
   );

   input         clk;
   input 	 wr0a;
   input 	 wr0b;
   input 	 wr1a;
   input 	 wr1b;
   input [15:0]  inData;

   output [15:0] out0;
   output [15:0] out1;

   reg [15:0] 	 mem [1:0];
   reg [15:0] 	 memtemp2 [1:0];
   reg [15:0] 	 memtemp3 [1:0];

   assign 	 out0 = {mem[0] ^ memtemp2[0]};
   assign 	 out1 = {mem[1] ^ memtemp3[1]};

   always @(posedge clk) begin
      // These mem assignments must be done in order after processing
      if (wr0a) begin
	 memtemp2[0] <= inData;
	 mem[0] <=  inData;
      end
      if (wr0b) begin
	 memtemp3[0] <= inData;
	 mem[0] <= ~inData;
      end
      if (wr1a) begin
	 memtemp3[1] <= inData;
	 mem[1] <=  inData;
      end
      if (wr1b) begin
	 memtemp2[1] <= inData;
	 mem[1] <= ~inData;
      end
   end

endmodule
