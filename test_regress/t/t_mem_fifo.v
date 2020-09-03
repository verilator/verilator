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

   wire [65:0]		outData;		// From fifo of fifo.v
   wire [15:0] 		inData = crc[15:0];
   wire [1:0] 		inWordPtr = crc[17:16];
   wire			wrEn = crc[20];
   wire [1:0] 		wrPtr = crc[33:32];
   wire [1:0] 		rdPtr = crc[34:33];

   fifo fifo (
	      // Outputs
	      .outData			(outData[65:0]),
	      // Inputs
	      .clk			(clk),
	      .inWordPtr		(inWordPtr[1:0]),
	      .inData			(inData[15:0]),
	      .rdPtr			(rdPtr),
	      .wrPtr			(wrPtr),
	      .wrEn			(wrEn));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%b q=%x\n",$time, cyc, crc, outData);
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc==90) begin
	 if (outData[63:0] != 64'hd9bcbc276f0984ea) $stop;
      end
      else if (cyc==91) begin
	 if (outData[63:0] != 64'hef77cd9b13a866f0) $stop;
      end
      else if (cyc==92) begin
	 if (outData[63:0] != 64'h2750cd9b13a866f0) $stop;
      end
      else if (cyc==93) begin
	 if (outData[63:0] != 64'h4ea0bc276f0984ea) $stop;
      end
      else if (cyc==94) begin
	 if (outData[63:0] != 64'h9d41bc276f0984ea) $stop;
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module fifo (/*AUTOARG*/
   // Outputs
   outData,
   // Inputs
   clk, inWordPtr, inData, wrPtr, rdPtr, wrEn
   );

   parameter fifoDepthLog2 = 1;
   parameter fifoDepth   = 1<<fifoDepthLog2;

`define PTRBITS   (fifoDepthLog2+1)
`define PTRBITSM1  fifoDepthLog2
`define PTRBITSM2 (fifoDepthLog2-1)

   input         clk;
   input [1:0] 	 inWordPtr;
   input [15:0]  inData;
   input [`PTRBITSM1:0] wrPtr;
   input [`PTRBITSM1:0] rdPtr;

   output [65:0] outData;
   input 	 wrEn;

   reg [65:0] outData;

   // verilator lint_off VARHIDDEN
   // verilator lint_off LITENDIAN
   reg [65:0] 	 fifo[0:fifoDepth-1];
   // verilator lint_on LITENDIAN
   // verilator lint_on VARHIDDEN

   //reg [65:0] 	      temp;

   always @(posedge clk) begin
      //$write ("we=%x PT=%x ID=%x D=%x\n", wrEn, wrPtr[`PTRBITSM2:0], {1'b0,~inWordPtr,4'b0}, inData[15:0]);
      if (wrEn) begin
	 fifo[ wrPtr[`PTRBITSM2:0] ][{1'b0,~inWordPtr,4'b0}+:16] <= inData[15:0];
	 // Equivelent to:
	 //temp = fifo[ wrPtr[`PTRBITSM2:0] ];
	 //temp [{1'b0,~inWordPtr,4'b0}+:16] = inData[15:0];
	 //fifo[ wrPtr[`PTRBITSM2:0] ] <= temp;
      end
      outData <= fifo[rdPtr[`PTRBITSM2:0]];
   end

endmodule
