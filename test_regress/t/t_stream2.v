// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [67:0]		left;			// From test of Test.v
   wire [67:0]		right;			// From test of Test.v
   // End of automatics

   wire [6:0] 	amt = crc[6:0];
   wire [67:0] 	in = {crc[3:0], crc[63:0]};

   Test test (/*AUTOINST*/
	      // Outputs
	      .left			(left[67:0]),
	      .right			(right[67:0]),
	      // Inputs
	      .amt			(amt[6:0]),
	      .in			(in[67:0]));

   wire [63:0] result = (left[63:0] ^ {60'h0, left[67:64]}
			 ^ right[63:0] ^ {60'h0, right[67:64]});

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x amt=%x left=%x right=%x\n",
	     $time, cyc, crc, result, amt, left, right);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 sum <= 64'h0;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h0da01049b480c38a
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   left, right,
   // Inputs
   amt, in
   );

   input [6:0] 	amt;
   input [67:0] in;

   // amt must be constant
   output wire [67:0] left;
   output wire [67:0] right;
   assign right = { << 33 {in}};
   assign left = { >> 33 {in}};

endmodule
