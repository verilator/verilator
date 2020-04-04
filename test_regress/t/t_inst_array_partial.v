// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [19:10] bitout;
   wire [29:24] short_bitout;
   wire [7:0] 	allbits;
   wire [15:0] 	twobits;

   sub
     i_sub1 [7:4] (.allbits (allbits),
		   .twobits (twobits[15:8]),
		   .bitout (bitout[17:14])),
     i_sub2 [3:0] (.allbits (allbits),
		   .twobits (twobits[7:0]),
		   .bitout (bitout[13:10]));

   sub
     i_sub3 [7:4] (.allbits (allbits),
		   .twobits (twobits[15:8]),
		   .bitout (bitout[17:14]));

   sub
     i_sub4 [7:4] (.allbits (allbits),
		   .twobits (twobits[15:8]),
		   .bitout (short_bitout[27:24]));

   sub
     i_sub5 [7:0] (.allbits (allbits),
		   .twobits (twobits),
		   .bitout (bitout[17:10]));

   sub
     i_sub6 [7:4] (.allbits (allbits),
		   .twobits (twobits[15:8]),
		   .bitout ({bitout[18+:2],short_bitout[28+:2]}));

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Signals under test
   assign allbits = crc[7:0];
   assign twobits = crc[15:0];
   wire [63:0] result = {48'h0, short_bitout, bitout};

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
`define EXPECTED_SUM 64'ha1da9ff8082a4ff6
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule // t


module sub
  ( input wire  [7:0] allbits,
    input wire  [1:0] twobits,
    output wire       bitout);

   assign bitout = (^ twobits) ^ (^ allbits);

endmodule // sub
