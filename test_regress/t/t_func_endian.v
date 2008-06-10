// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0]  in = crc[31:0];
   wire  	noswap = crc[32];
   wire 	nibble = crc[33];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0] 		out;			// From test of Test.v
   wire [31:0] 		swapped;		// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[31:0]),
	      .swapped			(swapped[31:0]),
	      // Inputs
	      .clk			(clk),
	      .noswap			(noswap),
	      .nibble			(nibble),
	      .in			(in[31:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== 64'h89522c3f5e5ca324) $stop;
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   out, swapped,
   // Inputs
   clk, noswap, nibble, in
   );
   input clk;

   input noswap;
   input nibble;

   input  [31:0] in;
   output [31:0] out;
   output [31:0] swapped;

   function [7:0] EndianSwap;
      input Nibble;
      input [7:0] Data;
      begin
         EndianSwap = (Nibble ? { Data[0], Data[1], Data[2], Data[3],
				  Data[4], Data[5], Data[6], Data[7] }
                       : { 4'h0, Data[0], Data[1], Data[2], Data[3] });
      end
   endfunction

   assign out[31:24] = (noswap ? in[31:24]
			: EndianSwap(nibble, in[31:24]));
   assign out[23:16] = (noswap ? in[23:16]
			: EndianSwap(nibble, in[23:16]));
   assign out[15:8]  = (noswap ? in[15:8]
			: EndianSwap(nibble, in[15:8]));
   assign out[7:0]   = (noswap ? in[7:0]
			: EndianSwap(nibble, in[7:0]));

   reg [31:0] swapped;
   always @(posedge clk) begin
      swapped[31:24] <= EndianSwap(nibble, in[31:24]);
      swapped[23:16] <= EndianSwap(nibble, in[23:16]);
      swapped[15:8]  <= EndianSwap(nibble, in[15:8] );
      swapped[7:0]   <= EndianSwap(nibble, in[7:0]  );
   end
endmodule
