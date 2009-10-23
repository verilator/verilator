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

   // Take CRC data and apply to testblock inputs
   wire [2:0]  in = (crc[1:0]==0 ? 3'd0
		     : crc[1:0]==0 ? 3'd1
		     : crc[1:0]==0 ? 3'd2 : 3'd4);

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]		out;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[31:0]),
	      // Inputs
	      .clk			(clk),
	      .in			(in[2:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, out};

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
`define EXPECTED_SUM 64'h704ca23e2a83e1c5
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in
   );

   // Replace this module with the device under test.
   //
   // Change the code in the t module to apply values to the inputs and
   // merge the output values into the result vector.

   input clk;
   input [2:0] in;
   output reg [31:0] out;

   localparam ST_0  = 0;
   localparam ST_1  = 1;
   localparam ST_2  = 2;

   always @(posedge clk) begin
      case (1'b1) // synopsys parallel_case
	in[ST_0]: out <= 32'h1234;
	in[ST_1]: out <= 32'h4356;
	in[ST_2]: out <= 32'h9874;
	default:  out <= 32'h1;
      endcase
   end
endmodule
