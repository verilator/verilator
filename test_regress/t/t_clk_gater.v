// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;
   reg		reset;
   reg		enable;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]		out;			// From test of Test.v
   // End of automatics

   // Take CRC data and apply to testblock inputs
   wire [31:0]  in = crc[31:0];

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[31:0]),
	      // Inputs
	      .clk			(clk),
	      .reset			(reset),
	      .enable			(enable),
	      .in			(in[31:0]));

   wire [63:0] result = {32'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      reset  <= (cyc < 5);
      enable <= cyc[4] || (cyc < 2);
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
`define EXPECTED_SUM 64'h01e1553da1dcf3af
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
   clk, reset, enable, in
   );

   input clk;
   input reset;
   input enable;
   input [31:0] in;
   output [31:0] out;


   // No gating
   reg [31:0] 	 d10;
   always @(posedge clk) begin
      d10 <= in;
   end

   reg displayit;
`ifdef VERILATOR  // Harder test
   initial displayit = $c1("0");  // Something that won't optimize away
`else
   initial displayit = '0;
`endif

   // Obvious gating + PLI
   reg [31:0] 	 d20;
   always @(posedge clk) begin
      if (enable) begin
	 d20 <= d10;  // Obvious gating
	 if (displayit) begin
	    $display("hello!");  // Must glob with other PLI statements
	 end
      end
   end

   // Reset means second-level gating
   reg [31:0] 	 d30, d31a, d31b, d32;
   always @(posedge clk) begin
      d32 <= d31b;
      if (reset) begin
	 d30 <= 32'h0;
	 d31a <= 32'h0;
	 d31b <= 32'h0;
	 d32 <= 32'h0;  // Overlaps above, just to make things interesting
      end
      else begin
	 // Mix two outputs
	 d30 <= d20;
	 if (enable) begin
	    d31a <= d30;
	    d31b <= d31a;
	 end
      end
   end

   // Multiple ORs for gater
   reg [31:0] 	 d40a,d40b;
   always @(posedge clk) begin
      if (reset) begin
	 d40a <= 32'h0;
	 d40b <= 32'h0;
      end
      if (enable) begin
	 d40a <= d32;
	 d40b <= d40a;
      end
   end

   // Non-optimizable
   reg [31:0] d91, d92;
   reg [31:0] inverted;
   always @(posedge clk) begin
      inverted = ~d40b;
      if (reset) begin
	 d91 <= 32'h0;
      end
      else begin
	 if (enable) begin
	    d91 <= inverted;
	 end
	 else begin
	    d92 <= inverted ^ 32'h12341234;  // Inverted gating condition
	 end
      end
   end

   wire [31:0] out = d91 ^ d92;

endmodule
