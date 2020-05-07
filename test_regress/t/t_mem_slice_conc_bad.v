// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// bug354

typedef logic [5:0]  data_t;

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire 	rst;
   data_t 	iii_in = crc[5:0];
   data_t 	jjj_in = crc[11:6];
   data_t	iii_out;
   data_t	jjj_out;
   logic [1:0]	ctl0 = crc[63:62];

   aaa aaa (.*);

   // Aggregate outputs into a single result vector
   wire [63:0] result = {64'h0};

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
	 rst <= 1'b0;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
	 rst <= 1'b1;
      end
      else if (cyc<90) begin
	 rst <= 1'b0;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h4afe43fb79d7b71e
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module bbb
   (
    output data_t   ggg_out[1:0],
    input data_t    ggg_in [1:0],
    input [1:0] [1:0] ctl,

    input logic    clk,
    input logic    rst
    );

   genvar 	   i;

   generate
      for (i=0; i<2; i++) begin: PPP
	 always_ff @(posedge clk) begin
	    if (rst) begin
	       ggg_out[i] <= 6'b0;
	    end
	    else begin
	       if (ctl[i][0]) begin
		  if (ctl[i][1]) begin
		     ggg_out[i] <= ~ggg_in[i];
		  end else begin
		     ggg_out[i] <= ggg_in[i];
		  end
	       end
	    end
	 end
      end
   endgenerate

endmodule

module aaa
   (
    input  data_t iii_in,
    input  data_t jjj_in,
    input  [1:0] ctl0,
    output data_t iii_out,
    output data_t jjj_out,
    input  logic clk,
    input  logic rst
    );

   // Below is a bug; {} concat isn't used to make arrays
  bbb bbb (
	   .ggg_in  ({jjj_in,            iii_in}),
	   .ggg_out ({jjj_out,           iii_out}),
	   .ctl	    ({{1'b1,ctl0[1]},    {1'b0,ctl0[0]}}),
           .*);

endmodule
