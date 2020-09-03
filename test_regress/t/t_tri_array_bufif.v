// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   parameter DW = 4;
   wire [3:0]  drv_a = crc[3:0];
   wire [3:0]  drv_b = crc[7:4];
   wire [3:0]  drv_e = crc[19:16];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [DW-1:0]	drv;			// To/From test1 of Test1.v
   wire [DW-1:0]	drv2;			// From test2 of Test2.v
   // End of automatics

   Test1 test1 (/*AUTOINST*/
		// Inouts
		.drv			(drv[DW-1:0]),
		// Inputs
		.drv_a			(drv_a[DW-1:0]),
		.drv_b			(drv_b[DW-1:0]),
		.drv_e			(drv_e[DW-1:0]));
   Test2 test2 (/*AUTOINST*/
		// Outputs
		.drv2			(drv2[DW-1:0]),
		// Inputs
		.drv_a			(drv_a[DW-1:0]),
		.drv_b			(drv_b[DW-1:0]),
		.drv_e			(drv_e[DW-1:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0, drv};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x drv=%x %x  (%b??%b:%b)\n",$time, cyc, crc, drv, drv2, drv_e,drv_a,drv_b);
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
	 if (drv2 != drv) $stop;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'hd95d216c5a2945d0
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test1 #(
  parameter DW = 4
)(
  input  wire [DW-1:0] drv_a,
  input  wire [DW-1:0] drv_b,
  input  wire [DW-1:0] drv_e,
  inout  wire [DW-1:0] drv
);

   wire   drv_0, drv_1, drv_2, drv_3;
   bufif1 bufa0  (drv_0, drv_a[0],  drv_e[0]);
   bufif1 bufb0  (drv_0, drv_b[0], ~drv_e[0]);
   bufif1 bufa1  (drv_1, drv_a[1],  drv_e[1]);
   bufif1 bufb1  (drv_1, drv_b[1], ~drv_e[1]);
   bufif1 bufa2  (drv_2, drv_a[2],  drv_e[2]);
   bufif1 bufb2  (drv_2, drv_b[2], ~drv_e[2]);
   bufif1 bufa3  (drv_3, drv_a[3],  drv_e[3]);
   bufif1 bufb3  (drv_3, drv_b[3], ~drv_e[3]);
   assign drv = {drv_3,drv_2,drv_1,drv_0};

endmodule

module Test2 #(
  parameter DW = 4
)(
  input  wire [DW-1:0] drv_a,
  input  wire [DW-1:0] drv_b,
  input  wire [DW-1:0] drv_e,
  inout  wire [DW-1:0] drv2
);

   wire [DW-1:0]       drv_all;
   bufif1 bufa [DW-1:0] (drv_all, drv_a, drv_e);
   // Below ~= bufif1 bufb [DW-1:0] (drv_all, drv_b, ~drv_e);
   bufif1 bufb [DW-1:0] ({drv_all[3], drv_all[2], drv_all[1], drv_all[0]},
			 {drv_b[3], drv_b[2], drv_b[1], drv_b[0]},
			 {~drv_e[3], ~drv_e[2], ~drv_e[1], ~drv_e[0]});
   assign drv2 = drv_all;

endmodule
