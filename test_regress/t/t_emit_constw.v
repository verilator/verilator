// DESCRIPTION: Verilator: Verilog Test module

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   reg [2*32-1:0]  w2;  initial w2  = {2 {32'h12345678}};
   reg [9*32-1:0]  w9;  initial w9  = {9 {32'h12345678}};
   reg [10*32-1:0] w10; initial w10 = {10{32'h12345678}};
   reg [11*32-1:0] w11; initial w11 = {11{32'h12345678}};
   reg [15*32-1:0] w15; initial w15 = {15{32'h12345678}};
   reg [31*32-1:0] w31; initial w31 = {31{32'h12345678}};
   reg [47*32-1:0] w47; initial w47 = {47{32'h12345678}};
   reg [63*32-1:0] w63; initial w63 = {63{32'h12345678}};

   // Aggregate outputs into a single result vector
   wire [63:0] result = (w2[63:0]
			 ^ w9[64:1]
			 ^ w10[65:2]
			 ^ w11[66:3]
			 ^ w15[67:4]
			 ^ w31[68:5]
			 ^ w47[69:6]
			 ^ w63[70:7]);

   // What checksum will we end up with
`define EXPECTED_SUM 64'h184cb39122d8c6e3

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
	 w2  <= w2  >> 1;
	 w9  <= w9  >> 1;
	 w10 <= w10 >> 1;
	 w11 <= w11 >> 1;
	 w15 <= w15 >> 1;
	 w31 <= w31 >> 1;
	 w47 <= w47 >> 1;
	 w63 <= w63 >> 1;
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
