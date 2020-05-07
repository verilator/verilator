// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//    --------------------------------------------------------
//    Bug Description:
//
//    Issue:  The gated clock gclk_vld[0] toggles but dvld[0]
//    input to the flop does not propagate to the output
//    signal entry_vld[0] correctly. The value that propagates
//    is the new value of dvld[0] not the one just before the
//    posedge of gclk_vld[0].
//    --------------------------------------------------------

// Define to see the bug with test failing with gated clock 'gclk_vld'
// Comment out the define to see the test passing with ungated clock 'clk'
`define GATED_CLK_TESTCASE 1

// A side effect of the problem is this warning, disabled by default
//verilator lint_on IMPERFECTSCH

// Test Bench
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;

   // Take CRC data and apply to testblock inputs
   wire [7:0]  dvld = crc[7:0];
   wire [7:0]  ff_en_e1 = crc[15:8];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]		entry_vld;		// From test of Test.v
   wire [7:0]		ff_en_vld;		// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .ff_en_vld		(ff_en_vld[7:0]),
	      .entry_vld		(entry_vld[7:0]),
	      // Inputs
	      .clk			(clk),
	      .dvld			(dvld[7:0]),
	      .ff_en_e1			(ff_en_e1[7:0]));

   reg err_code;
   reg ffq_clk_active;
   reg [7:0] prv_dvld;

   initial begin
     err_code = 0;
     ffq_clk_active = 0;
   end
   always @ (posedge clk) begin
     prv_dvld = test.dvld;
   end
   always @ (negedge test.ff_entry_dvld_0.clk) begin
     ffq_clk_active = 1;
     if (test.entry_vld[0] !== prv_dvld[0]) err_code = 1;
   end

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x ",$time, cyc, crc);
      $display(" en=%b fen=%b d=%b ev=%b",
	       test.flop_en_vld[0],  test.ff_en_vld[0],
	       test.dvld[0],  test.entry_vld[0]);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc<3) begin
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x\n",$time, cyc, crc);
         if (ffq_clk_active == 0) begin
           $display ("----");
           $display ("%%Error: TESTCASE FAILED with no Clock arriving at FFQs");
           $display ("----");
           $stop;
         end
         else if (err_code) begin
           $display ("----");
           $display ("%%Error: TESTCASE FAILED with invalid propagation of 'd' to 'q' of FFQs");
           $display ("----");
           $stop;
         end
         else begin
	   $write("*-* All Finished *-*\n");
	   $finish;
        end
      end
   end

endmodule

module llq (clk, d, q);
   parameter WIDTH = 32;
   input clk;
   input [WIDTH-1:0] d;
   output [WIDTH-1:0] q;

   reg [WIDTH-1:0]    qr;

   /* verilator lint_off COMBDLY */

   always @(clk or d)
     if (clk == 1'b0)
       qr <= d;

   /* verilator lint_on COMBDLY */

   assign q = qr;
endmodule

module ffq (clk, d, q);
   parameter WIDTH = 32;
   input clk;
   input [WIDTH-1:0] d;
   output [WIDTH-1:0] q;

   reg [WIDTH-1:0]    qr;

   always @(posedge clk)
     qr <= d;

   assign q = qr;
endmodule

// DUT module
module Test (/*AUTOARG*/
   // Outputs
   ff_en_vld, entry_vld,
   // Inputs
   clk, dvld, ff_en_e1
   );
   input clk;

   input [7:0] dvld;
   input [7:0] ff_en_e1;

   output [7:0] ff_en_vld;
   output wire [7:0] entry_vld;

   wire [7:0] gclk_vld;
   wire [7:0] ff_en_vld /*verilator clock_enable*/;
   reg [7:0] flop_en_vld;

   always @(posedge clk) flop_en_vld <= ff_en_e1;

   // clock gating
`ifdef GATED_CLK_TESTCASE
   assign gclk_vld = {8{clk}} & ff_en_vld;
`else
   assign gclk_vld = {8{clk}};
`endif

   // latch for avoiding glitch on the clock gating control
   llq  #(8)  dp_ff_en_vld (.clk(clk), .d(flop_en_vld), .q(ff_en_vld));

   // flops that use the gated clock signal
   ffq  #(1)  ff_entry_dvld_0 (.clk(gclk_vld[0]), .d(dvld[0]), .q(entry_vld[0]));
   ffq  #(1)  ff_entry_dvld_1 (.clk(gclk_vld[1]), .d(dvld[1]), .q(entry_vld[1]));
   ffq  #(1)  ff_entry_dvld_2 (.clk(gclk_vld[2]), .d(dvld[2]), .q(entry_vld[2]));
   ffq  #(1)  ff_entry_dvld_3 (.clk(gclk_vld[3]), .d(dvld[3]), .q(entry_vld[3]));
   ffq  #(1)  ff_entry_dvld_4 (.clk(gclk_vld[4]), .d(dvld[4]), .q(entry_vld[4]));
   ffq  #(1)  ff_entry_dvld_5 (.clk(gclk_vld[5]), .d(dvld[5]), .q(entry_vld[5]));
   ffq  #(1)  ff_entry_dvld_6 (.clk(gclk_vld[6]), .d(dvld[6]), .q(entry_vld[6]));
   ffq  #(1)  ff_entry_dvld_7 (.clk(gclk_vld[7]), .d(dvld[7]), .q(entry_vld[7]));

endmodule
