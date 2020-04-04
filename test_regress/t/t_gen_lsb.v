// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [3:0]   datai = crc[3:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [3:0]		datao;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .datao			(datao[3:0]),
	      // Inputs
	      .clk			(clk),
	      .datai			(datai[3:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0, datao};

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
`define EXPECTED_SUM 64'h3db7bc8bfe61f983
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test
  (
   input logic 	      clk,
   input logic [3:0]  datai,
   output logic [3:0] datao
);
   genvar 	      i;

   parameter SIZE = 4;

   logic [SIZE:1][3:0] 	delay;

   always_ff @(posedge clk) begin
      delay[1][3:0] <= datai;
   end

   generate
      for (i = 2; i < (SIZE+1); i++) begin
         always_ff @(posedge clk) begin
            delay[i][3:0] <= delay[i-1][3:0];
         end
      end
   endgenerate

   always_comb datao = delay[SIZE][3:0];

endmodule
