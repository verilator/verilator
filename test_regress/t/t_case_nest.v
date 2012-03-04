// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=0;
   reg [63:0] crc;
   reg [63:0] sum;

   reg 	      out1;
   sub sub (.in(crc[23:0]), .out1(out1));

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x sum=%x out=%x\n",$time, cyc, crc, sum, out1);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {sum[62:0], sum[63]^sum[2]^sum[0]} ^ {63'h0,out1};
      if (cyc==1) begin
	 // Setup
	 crc <= 64'h00000000_00000097;
	 sum <= 64'h0;
      end
      else if (cyc==90) begin
	 if (sum !== 64'h2e5cb972eb02b8a0) $stop;
      end
      else if (cyc==91) begin
      end
      else if (cyc==92) begin
      end
      else if (cyc==93) begin
      end
      else if (cyc==94) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module sub (/*AUTOARG*/
   // Outputs
   out1,
   // Inputs
   in
   );

   input      [23:0] in;
   output reg [0:0] out1;  // Note this tests a vector of 1 bit, which is different from a non-arrayed signal

   parameter [1023:0] RANDOM = 1024'b101011010100011011100111101001000000101000001111111111100110000110011011010110011101000100110000110101111101000111100100010111001001110001010101000111000100010000010011100001100011110110110000101100011111000110111110010110011000011111111010101110001101010010001111110111100000110111101100110101110001110110000010000110101110111001111001100001101110001011100111001001110101001010000110101010100101111000010000010110100101110100110000110110101000100011101111100011000110011001100010010011001101100100101110010100110101001110011111110010000111001111000010001101100101101110111110001000010110010011100101001011111110011010110111110000110010011110001110110011010011010110011011111001110100010110100011100001011000101111000010011111010111001110110011101110101011111001100011000101000001000100111110010100111011101010101011001101000100000101111110010011010011010001111010001110000110010100011110110011001010000011001010010110111101010010011111111010001000101100010100100010011001100110000111111000001000000001001111101110000100101;

   always @* begin
      casez (in[17:16])
	2'b00: casez (in[2:0])
		 3'h0:	out1[0] = in[0]^RANDOM[0];
		 3'h1:	out1[0] = in[0]^RANDOM[1];
		 3'h2:	out1[0] = in[0]^RANDOM[2];
		 3'h3:	out1[0] = in[0]^RANDOM[3];
		 3'h4:	out1[0] = in[0]^RANDOM[4];
		 3'h5:	out1[0] = in[0]^RANDOM[5];
		 3'h6:	out1[0] = in[0]^RANDOM[6];
		 3'h7:	out1[0] = in[0]^RANDOM[7];
	       endcase
	2'b01: casez (in[2:0])
		 3'h0:	out1[0] = RANDOM[10];
		 3'h1:	out1[0] = RANDOM[11];
		 3'h2:	out1[0] = RANDOM[12];
		 3'h3:	out1[0] = RANDOM[13];
		 3'h4:	out1[0] = RANDOM[14];
		 3'h5:	out1[0] = RANDOM[15];
		 3'h6:	out1[0] = RANDOM[16];
		 3'h7:	out1[0] = RANDOM[17];
	       endcase
	2'b1?: casez (in[4])
		 1'b1: casez (in[2:0])
			 3'h0:	out1[0] = RANDOM[20];
			 3'h1:	out1[0] = RANDOM[21];
			 3'h2:	out1[0] = RANDOM[22];
			 3'h3:	out1[0] = RANDOM[23];
			 3'h4:	out1[0] = RANDOM[24];
			 3'h5:	out1[0] = RANDOM[25];
			 3'h6:	out1[0] = RANDOM[26];
			 3'h7:	out1[0] = RANDOM[27];
		       endcase
		 1'b0: casez (in[2:0])
			 3'h0:	out1[0] = RANDOM[30];
			 3'h1:	out1[0] = RANDOM[31];
			 3'h2:	out1[0] = RANDOM[32];
			 3'h3:	out1[0] = RANDOM[33];
			 3'h4:	out1[0] = RANDOM[34];
			 3'h5:	out1[0] = RANDOM[35];
			 3'h6:	out1[0] = RANDOM[36];
			 3'h7:	out1[0] = RANDOM[37];
		       endcase
	       endcase
      endcase
      end

endmodule
