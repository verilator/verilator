// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

// bug823
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [2:0]  in = crc[2:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]		mask;			// From test of Test.v
   wire [3:0]		out;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[3:0]),
	      .mask			(mask[3:0]),
	      // Inputs
	      .clk			(clk),
	      .in			(in[2:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0, out & mask};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x out=%b mask=%b\n",$time, cyc, crc, out, mask);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 sum <= '0;
      end
      else if (cyc<10) begin
	 sum <= '0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'ha9d3a7a69d2bea75
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   out, mask,
   // Inputs
   clk, in
   );

   input clk;
   input [2:0] in;
   output reg [3:0] out;
   output reg [3:0] mask;
   localparam [15:5] p = 11'h1ac;

   always @(posedge clk) begin
      // verilator lint_off WIDTH
      out <= p[15 + in -: 5];
      // verilator lint_on WIDTH
      mask[3] <= ((15 + in - 5) < 12);
      mask[2] <= ((15 + in - 5) < 13);
      mask[1] <= ((15 + in - 5) < 14);
      mask[0] <= ((15 + in - 5) < 15);
   end

endmodule
