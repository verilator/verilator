// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   wire [31:0]  inp = crc[31:0];
   wire		reset = (cyc < 5);

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]		outp;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .outp			(outp[31:0]),
	      // Inputs
	      .reset			(reset),
	      .clk			(clk),
	      .inp			(inp[31:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, outp};

   // What checksum will we end up with
`define EXPECTED_SUM 64'ha7f0a34f9cf56ccb

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
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   outp,
   // Inputs
   reset, clk, inp
   );

   input		  reset;
   input		  clk;
   input [31:0] 	  inp;
   output [31:0] 	  outp;

   function [31:0] no_inline_function;
      input [31:0] 	  var1;
      input [31:0] 	  var2;
      /*verilator no_inline_task*/
      reg [31*2:0] 	  product1 ;
      reg [31*2:0] 	  product2 ;
      integer 		  i;
      reg [31:0] 	  tmp;

      begin
	 product2 = {(31*2+1){1'b0}};

	 for (i = 0; i < 32; i = i + 1)
	   if (var2[i]) begin
	      product1 = { {31*2+1-32{1'b0}}, var1} << i;
	      product2 = product2 ^ product1;
	   end
	 no_inline_function = 0;

	 for (i= 0; i < 31; i = i + 1 )
	   no_inline_function[i+1] = no_inline_function[i] ^ product2[i] ^ var1[i];
      end
   endfunction

   reg [31:0] outp;
   reg [31:0] inp_d;

   always @( posedge clk ) begin
      if( reset ) begin
	 outp <= 0;
      end
      else begin
	 inp_d <= inp;
	 outp <= no_inline_function(inp, inp_d);
      end
   end

endmodule
