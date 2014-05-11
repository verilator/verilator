// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0]  in = crc[31:0];

   localparam WIDTH = 31;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [WIDTH-1:0]	b;			// From test of Test.v
   wire [WIDTH-1:0]	c;			// From test of Test.v
   // End of automatics
   reg 			rst_l;

   Test #(.WIDTH(WIDTH))
   test (/*AUTOINST*/
	 // Outputs
	 .b				(b[WIDTH-1:0]),
	 .c				(c[WIDTH-1:0]),
	 // Inputs
	 .clk				(clk),
	 .rst_l				(rst_l),
	 .in				(in[WIDTH-1:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {1'h0, c, 1'b0, b};

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
	 rst_l <= ~1'b1;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
	 rst_l <= ~1'b1;
	 // Hold reset while summing
      end
      else if (cyc<20) begin
	 rst_l <= ~1'b0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'hbcfcebdb75ec9d32
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   b, c,
   // Inputs
   clk, rst_l, in
   );

   parameter    WIDTH = 5;

   input                 clk;
   input 		 rst_l;

   input [WIDTH-1:0] 	 in;
   output wire [WIDTH-1:0] 	b;
   output wire [WIDTH-1:0] 	c;

   dff # ( .WIDTH	(WIDTH),
	   .RESET	('0),   // Although this is a single bit, the parameter must be the specified type
	   .RESET_WIDTH (1) )
   sub1
     ( .clk(clk), .rst_l(rst_l), .q(b), .d(in) );

   dff # ( .WIDTH	(WIDTH),
	   .RESET	({ 1'b1, {(WIDTH-1){1'b0}} }),
	   .RESET_WIDTH (WIDTH))
   sub2
     ( .clk(clk), .rst_l(rst_l), .q(c), .d(in) );

endmodule

module dff (/*AUTOARG*/
   // Outputs
   q,
   // Inputs
   clk, rst_l, d
   );

   parameter WIDTH = 1;
   parameter RESET = {WIDTH{1'b0}};
   parameter RESET_WIDTH = WIDTH;

   input   clk;
   input   rst_l;
   input [WIDTH-1:0] d;
   output reg [WIDTH-1:0] q;

   always_ff @(posedge clk or negedge rst_l) begin
      if ($bits(RESET) != RESET_WIDTH) $stop;
      // verilator lint_off WIDTH
      if (~rst_l) q <= RESET;
      // verilator lint_on WIDTH
      else q <= d;
   end
endmodule
