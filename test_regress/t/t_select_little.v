// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // verilator lint_off LITENDIAN
   wire [10:41] sel2 = crc[31:0];
   wire [10:100] sel3 = {crc[26:0],crc};

   wire		 out20 = sel2[{1'b0,crc[3:0]} + 11];
   wire [3:0] 	 out21 = sel2[13 : 16];
   wire [3:0] 	 out22 = sel2[{1'b0,crc[3:0]} + 20 +: 4];
   wire [3:0] 	 out23 = sel2[{1'b0,crc[3:0]} + 20 -: 4];

   wire		 out30 = sel3[{2'b0,crc[3:0]} + 11];
   wire [3:0] 	 out31 = sel3[13 : 16];
   wire [3:0] 	 out32 = sel3[crc[5:0] + 20 +: 4];
   wire [3:0] 	 out33 = sel3[crc[5:0] + 20 -: 4];

   // Aggregate outputs into a single result vector
   wire [63:0] 	 result = {38'h0, out20, out21, out22, out23, out30, out31, out32, out33};

   reg [19:50] sel1;
   initial begin
      // Path clearing
      //        122333445
      //        826048260
      sel1 = 32'h12345678;
      if (sel1 != 32'h12345678) $stop;
      if (sel1[47 : 50] != 4'h8) $stop;
      if (sel1[31 : 34] != 4'h4) $stop;
      if (sel1[27 +: 4] != 4'h3) $stop; //==[27:30], in memory as [23:20]
      if (sel1[26 -: 4] != 4'h2) $stop; //==[23:26], in memory as [27:24]
   end

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] sels=%x,%x,%x,%x %x,%x,%x,%x\n",$time, out20,out21,out22,out23, out30,out31,out32,out33);
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
`define EXPECTED_SUM 64'h28bf65439eb12c00
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
