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

   wire [15:-16] sel2 = crc[31:0];
   wire [80:-10] sel3 = {crc[26:0],crc};

   wire [3:0] 	 out21 = sel2[-3 : -6];
   wire [3:0] 	 out22 = sel2[{1'b0,crc[3:0]} - 16 +: 4];
   wire [3:0] 	 out23 = sel2[{1'b0,crc[3:0]} - 10 -: 4];

   wire [3:0] 	 out31 = sel3[-3 : -6];
   wire [3:0] 	 out32 = sel3[crc[5:0] - 6 +: 4];
   wire [3:0] 	 out33 = sel3[crc[5:0] - 6 -: 4];

   // Aggregate outputs into a single result vector
   wire [63:0] result = {40'h0, out21, out22, out23, out31, out32, out33};

   reg [15:-16] sel1;
   initial begin
      // Path clearing
      sel1 = 32'h12345678;
      if (sel1 != 32'h12345678) $stop;
      if (sel1[-13 : -16] != 4'h8) $stop;
      if (sel1[3:0] != 4'h4) $stop;
      if (sel1[4 +: 4] != 4'h3) $stop;
      if (sel1[11 -: 4] != 4'h2) $stop;
   end

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] sels=%x,%x,%x %x,%x,%x\n",$time, out21,out22,out23, out31,out32,out33);
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
`define EXPECTED_SUM 64'hba7fe1e7ac128362
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
