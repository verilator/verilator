// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   parameter NPAD = 4;

   tri 		pad [NPAD-1:0];  // Array
   wire	[NPAD-1:0] data0 = crc[0 +: 4];
   wire	[NPAD-1:0] data1 = crc[8 +: 4];
   wire	[NPAD-1:0] en    = crc[16 +: 4];

   for (genvar g=0; g<NPAD; ++g) begin : gpad
      Pad pad1 (.pad(pad[g]),
		.ena(en[g]),
		.data(data1[g]));
      Pad pad0 (.pad(pad[g]),
		.ena(!en[g]),
		.data(data0[g]));
   end

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {60'h0, pad[3], pad[2], pad[1], pad[0]}
	     ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
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
`define EXPECTED_SUM 64'he09fe6f2dfd7a302
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Pad
  (inout pad,
   input ena,
   input data);
   assign pad = ena ? data : 1'bz;
endmodule
