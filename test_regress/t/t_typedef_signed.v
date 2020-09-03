// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug456

typedef logic signed [34:0] rc_t;

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [34:0]  rc = crc[34:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic		o;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .o			(o),
	      // Inputs
	      .rc			(rc),
	      .clk			(clk));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {63'h0, o};

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
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h7211d24a17b25ec9
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test( output logic o,
             input 	 rc_t rc,
             input logic clk);

   localparam RATIO = 2;

   rc_t rc_d[RATIO:1];

   always_ff @(posedge clk) begin
      integer  k;

      rc_d[1] <= rc;

      for( k=2; k<RATIO+1; k++ ) begin
         rc_d[k] <= rc_d[k-1];
      end
   end // always_ff @

   assign o = rc_d[RATIO] < 0;

endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
