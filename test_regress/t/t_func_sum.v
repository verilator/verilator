// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008-2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   wire [9:0]  I1 = crc[9:0];
   wire [9:0]  I2 = crc[19:10];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [9:0]		S;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .S			(S[9:0]),
	      // Inputs
	      .I1			(I1[9:0]),
	      .I2			(I2[9:0]));

   wire [63:0] result = {32'h0, 22'h0, S};

`define EXPECTED_SUM 64'h24c38b77b0fcc2e7

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
   S,
   // Inputs
   I1, I2
   );

   input [9:0] I1/*verilator public*/;
   input [9:0] I2/*verilator public*/;
   output reg [9:0] S/*verilator public*/;

   always @(I1 or I2)
     t2(I1,I2,S);

   task t1;
      input In1,In2;
      output Sum;
      Sum = In1 ^ In2;
   endtask

   task t2;
      input[9:0] In1,In2;
      output [9:0] Sum;
      integer 	   I;
      begin
	 for (I=0;I<10;I=I+1)
	   t1(In1[I],In2[I],Sum[I]);
      end
   endtask
endmodule
