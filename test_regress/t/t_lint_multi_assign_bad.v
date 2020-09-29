// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Peter Monsson.

// Issue #2188 (#2167, #1369)

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;
   wire [31:0] in = cyc;
   wire bad1;


   Test test (/*AUTOINST*/
	      // Inputs
	      .clk			(clk),
	      .in			(in[31:0]),
	      .bad1                     (bad1));

//   wire_test wt (.rst			(cyc>3),
//		 .in1			(cyc[0]),
//		 .in2			(cyc[1]),
//		 .mux			(cyc[2]),
//		 .out			(),
//		 /*AUTOINST*/
//		 // Inputs
//		 .clk			(clk));


   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

// Great! I'd suggest in V3Undriven, which looks for undriven nets,
// this would be a double-driven case. Please test cases with single
// bits multi-driven, and a whole bus driver with one bit driven, and
// likewise with assignments to Z. I don't think you'll be able to
// fully ignore Z's or will be too many false positives, perhaps any
// expression with a Z underneath turns off checking for that
// variable.

module Test (/*AUTOARG*/
   // Inputs
   clk, in, bad1
   );

   input clk;
   input [31:0] in;

   output wire 	bad1;

   //single bits / whole bus multidriven
   wire good0;
   assign good0 = 0;

   wire good1;
   assign good1 = 0;
   assign good1 = 'z;

   wire good2;
   assign good2 = 'z;
   assign good2 = 0;

   wire good4;
   assign good4 = in%2==1 ? in[1] : 'z;
   assign good4 = in%2==0 ? in[0] : 'z;

   wire bad0;
   assign bad0 = 0;
   assign bad0 = 1;
   assign bad0 = 0;

   assign bad1 = 0;
   assign bad1 = 1;

   wire bad2 = 0;
   assign bad2 = 1;

   // Initial blocks and assign
   reg good10;
   initial begin
      good10 = 0;
      good10 = 1;
   end

   reg bad10;
   initial bad10 = 0;
   assign bad10 = 1; //TODO: this is not failing

   reg bad11;
   assign bad11 = 0;
   initial bad11 = 1; //TODO: this is not failing

   reg bad12;
   initial bad12 = 0;
   initial bad12 = 1; //TODO: this is not failing

   //TODO: always (non-clock) and assign
   //TODO: all combinations of (always_comb'ish, always_ff'ish, initial, assign)

   reg good100;
   always @(*) begin
      good100 = 0;
      good100 = 1;
      if (in%2 == 1) begin
	 good100 = 0;
      end
   end

   // Selected bits multidriven

   wire [3:0] good200;
   assign good200[3:2] = 0;
   assign good200[1:0] = 0;

   wire [3:0] good201;
   assign good201[1:0] = 'z;
   assign good201[1:0] = 0;

   wire [3:0] good202;
   assign good202[1:0] = 0;
   assign good202[1:0] = 'z;

   wire [3:0] bad200;
   assign bad200[1:0] = 0;
   assign bad200[1:0] = 0;

   wire [3:0] bad201;
   assign bad201[1:0] = 0;
   assign bad201[2:1] = 1;

   wire [3:0] bad202;
   assign bad202 = 1;
   assign bad202[1:0] = 0;

   wire [3:0] bad203;
   assign bad203[1:0] = 1;
   assign bad203 = 0;

endmodule
