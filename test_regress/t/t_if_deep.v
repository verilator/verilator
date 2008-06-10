// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

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

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]		out;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[31:0]),
	      // Inputs
	      .clk			(clk),
	      .in			(in[31:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, out};

   // What checksum will we end up with
`define EXPECTED_SUM 64'h966e272fd829e672

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

module Test (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in
   );

   input clk;
   input  [31:0] in;
   output [31:0] out;

   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [31:0]		out;
   // End of automatics

`ifdef verilator
 `define dontOptimize $c1("1")
`else
 `define dontOptimize 1'b1
`endif

   always @(posedge clk) begin
      out <= in;
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
	if (in[0])
	  out <= ~in;
   end
endmodule
