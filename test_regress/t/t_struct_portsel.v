// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [19:0]  in = crc[19:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [19:0]		out;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[19:0]),
	      // Inputs
	      .in			(in[19:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {44'h0, out};

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
`define EXPECTED_SUM 64'hdb7bc61592f31b99
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

typedef struct packed {
   logic [7:0] cn;
   logic       vbfval;
   logic       vabval;
} rel_t;

module Test (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );

   input [19:0] in;
   output [19:0] out;

   rel_t [1:0] i; // From ifb0 of ifb.v, ...
   rel_t [1:0] o; // From ifb0 of ifb.v, ...

   assign i = in;
   assign out = o;

   sub sub
     (
      .i   (i[1:0]),
      .o   (o[1:0]));
endmodule

module sub (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   i
   );

   input                 rel_t [1:0] i;
   output                rel_t [1:0] o;
   assign o = i;
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
