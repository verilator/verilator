// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire 	pick1 = crc[0];
   wire [13:0][1:0] data1 = crc[27+1:1];
   wire [3:0][2:0][1:0] data2 = crc[23+29:29];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [15:0] [1:0]	datao;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .datao			(datao/*[15:0][1:0]*/),
	      // Inputs
	      .pick1			(pick1),
	      .data1			(data1/*[13:0][1:0]*/),
	      .data2			(data2/*[2:0][3:0][1:0]*/));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, datao};

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
`define EXPECTED_SUM 64'h3ff4bf0e6407b281
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test
  (
   input logic 			  pick1,
   input logic [13:0] [1:0] 	  data1, //    14 x 2 = 28 bits
   input logic [ 3:0] [2:0] [1:0] data2, // 4 x 3 x 2 = 24 bits
   output logic [15:0] [1:0] 	  datao   //    16 x 2 = 32 bits
   );
   // verilator lint_off WIDTH
   always_comb datao[13: 0]  // 28 bits
     = (pick1)
       ? {data1}  // 28 bits
       : {'0, data2};  // 25-28 bits, perhaps not legal as '0 is unsized
   // verilator lint_on WIDTH
   always_comb datao[15:14] = '0;
endmodule
