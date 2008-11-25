// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg  [9:0] index;
   wire [7:0] index0 = index[7:0] + 8'h0;
   wire [7:0] index1 = index[7:0] + 8'h1;
   wire [7:0] index2 = index[7:0] + 8'h2;
   wire [7:0] index3 = index[7:0] + 8'h3;
   wire [7:0] index4 = index[7:0] + 8'h4;
   wire [7:0] index5 = index[7:0] + 8'h5;
   wire [7:0] index6 = index[7:0] + 8'h6;
   wire [7:0] index7 = index[7:0] + 8'h7;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [9:0]		outa0;			// From s0 of t_case_huge_sub.v
   wire [9:0]		outa1;			// From s1 of t_case_huge_sub.v
   wire [9:0]		outa2;			// From s2 of t_case_huge_sub.v
   wire [9:0]		outa3;			// From s3 of t_case_huge_sub.v
   wire [9:0]		outa4;			// From s4 of t_case_huge_sub.v
   wire [9:0]		outa5;			// From s5 of t_case_huge_sub.v
   wire [9:0]		outa6;			// From s6 of t_case_huge_sub.v
   wire [9:0]		outa7;			// From s7 of t_case_huge_sub.v
   wire [1:0]		outb0;			// From s0 of t_case_huge_sub.v
   wire [1:0]		outb1;			// From s1 of t_case_huge_sub.v
   wire [1:0]		outb2;			// From s2 of t_case_huge_sub.v
   wire [1:0]		outb3;			// From s3 of t_case_huge_sub.v
   wire [1:0]		outb4;			// From s4 of t_case_huge_sub.v
   wire [1:0]		outb5;			// From s5 of t_case_huge_sub.v
   wire [1:0]		outb6;			// From s6 of t_case_huge_sub.v
   wire [1:0]		outb7;			// From s7 of t_case_huge_sub.v
   wire			outc0;			// From s0 of t_case_huge_sub.v
   wire			outc1;			// From s1 of t_case_huge_sub.v
   wire			outc2;			// From s2 of t_case_huge_sub.v
   wire			outc3;			// From s3 of t_case_huge_sub.v
   wire			outc4;			// From s4 of t_case_huge_sub.v
   wire			outc5;			// From s5 of t_case_huge_sub.v
   wire			outc6;			// From s6 of t_case_huge_sub.v
   wire			outc7;			// From s7 of t_case_huge_sub.v
   wire [9:0]		outq;			// From q of t_case_huge_sub4.v
   wire [3:0]		outr;			// From sub3 of t_case_huge_sub3.v
   wire [9:0]		outsmall;		// From sub2 of t_case_huge_sub2.v
   // End of automatics

   t_case_huge_sub2 sub2 (
			  // Outputs
			  .outa		(outsmall[9:0]),
			  /*AUTOINST*/
			  // Inputs
			  .index	(index[9:0]));

   t_case_huge_sub3 sub3 (/*AUTOINST*/
			  // Outputs
			  .outr		(outr[3:0]),
			  // Inputs
			  .clk		(clk),
			  .index	(index[9:0]));

   /* t_case_huge_sub AUTO_TEMPLATE (
		       .outa		(outa@[]),
		       .outb		(outb@[]),
		       .outc		(outc@[]),
		       .index		(index@[]));
    */

   t_case_huge_sub s0 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa0[9:0]),		 // Templated
		       .outb		(outb0[1:0]),		 // Templated
		       .outc		(outc0),		 // Templated
		       // Inputs
		       .index		(index0[7:0]));		 // Templated
   t_case_huge_sub s1 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa1[9:0]),		 // Templated
		       .outb		(outb1[1:0]),		 // Templated
		       .outc		(outc1),		 // Templated
		       // Inputs
		       .index		(index1[7:0]));		 // Templated
   t_case_huge_sub s2 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa2[9:0]),		 // Templated
		       .outb		(outb2[1:0]),		 // Templated
		       .outc		(outc2),		 // Templated
		       // Inputs
		       .index		(index2[7:0]));		 // Templated
   t_case_huge_sub s3 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa3[9:0]),		 // Templated
		       .outb		(outb3[1:0]),		 // Templated
		       .outc		(outc3),		 // Templated
		       // Inputs
		       .index		(index3[7:0]));		 // Templated
   t_case_huge_sub s4 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa4[9:0]),		 // Templated
		       .outb		(outb4[1:0]),		 // Templated
		       .outc		(outc4),		 // Templated
		       // Inputs
		       .index		(index4[7:0]));		 // Templated
   t_case_huge_sub s5 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa5[9:0]),		 // Templated
		       .outb		(outb5[1:0]),		 // Templated
		       .outc		(outc5),		 // Templated
		       // Inputs
		       .index		(index5[7:0]));		 // Templated
   t_case_huge_sub s6 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa6[9:0]),		 // Templated
		       .outb		(outb6[1:0]),		 // Templated
		       .outc		(outc6),		 // Templated
		       // Inputs
		       .index		(index6[7:0]));		 // Templated
   t_case_huge_sub s7 (/*AUTOINST*/
		       // Outputs
		       .outa		(outa7[9:0]),		 // Templated
		       .outb		(outb7[1:0]),		 // Templated
		       .outc		(outc7),		 // Templated
		       // Inputs
		       .index		(index7[7:0]));		 // Templated

   t_case_huge_sub4 q (/*AUTOINST*/
		       // Outputs
		       .outq		(outq[9:0]),
		       // Inputs
		       .index		(index[7:0]));


   integer cyc; initial cyc=1;
   initial index = 10'h0;

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 //$write("%x: %x\n",cyc,outr);
	 //$write("%x: %x %x %x %x\n", cyc, outa1,outb1,outc1,index1);
	 if (cyc==1) begin
	    index <= 10'h236;
	 end
	 if (cyc==2) begin
	    index <= 10'h022;
	    if (outsmall != 10'h282) $stop;
	    if (outr != 4'b0) $stop;
	    if ({outa0,outb0,outc0}!={10'h282,2'd3,1'b0}) $stop;
	    if ({outa1,outb1,outc1}!={10'h21c,2'd3,1'b1}) $stop;
	    if ({outa2,outb2,outc2}!={10'h148,2'd0,1'b1}) $stop;
	    if ({outa3,outb3,outc3}!={10'h3c0,2'd2,1'b0}) $stop;
	    if ({outa4,outb4,outc4}!={10'h176,2'd1,1'b1}) $stop;
	    if ({outa5,outb5,outc5}!={10'h3fc,2'd2,1'b1}) $stop;
	    if ({outa6,outb6,outc6}!={10'h295,2'd3,1'b1}) $stop;
	    if ({outa7,outb7,outc7}!={10'h113,2'd2,1'b1}) $stop;
	    if (outq != 10'h001) $stop;
	 end
	 if (cyc==3) begin
	    index <= 10'h165;
	    if (outsmall != 10'h191) $stop;
	    if (outr != 4'h5) $stop;
	    if ({outa1,outb1,outc1}!={10'h379,2'd1,1'b0}) $stop;
	    if ({outa2,outb2,outc2}!={10'h073,2'd0,1'b0}) $stop;
	    if ({outa3,outb3,outc3}!={10'h2fd,2'd3,1'b1}) $stop;
	    if ({outa4,outb4,outc4}!={10'h2e0,2'd3,1'b1}) $stop;
	    if ({outa5,outb5,outc5}!={10'h337,2'd1,1'b1}) $stop;
	    if ({outa6,outb6,outc6}!={10'h2c7,2'd3,1'b1}) $stop;
	    if ({outa7,outb7,outc7}!={10'h19e,2'd3,1'b0}) $stop;
	    if (outq != 10'h001) $stop;
	 end
	 if (cyc==4) begin
	    index <= 10'h201;
	    if (outsmall != 10'h268) $stop;
	    if (outr != 4'h2) $stop;
	    if ({outa1,outb1,outc1}!={10'h111,2'd1,1'b0}) $stop;
	    if ({outa2,outb2,outc2}!={10'h1f9,2'd0,1'b0}) $stop;
	    if ({outa3,outb3,outc3}!={10'h232,2'd0,1'b1}) $stop;
	    if ({outa4,outb4,outc4}!={10'h255,2'd3,1'b0}) $stop;
	    if ({outa5,outb5,outc5}!={10'h34c,2'd1,1'b1}) $stop;
	    if ({outa6,outb6,outc6}!={10'h049,2'd1,1'b1}) $stop;
	    if ({outa7,outb7,outc7}!={10'h197,2'd3,1'b0}) $stop;
	    if (outq != 10'h001) $stop;
	 end
	 if (cyc==5) begin
	    index <= 10'h3ff;
	    if (outr != 4'hd) $stop;
	    if (outq != 10'h001) $stop;
	 end
	 if (cyc==6) begin
	    index <= 10'h0;
	    if (outr != 4'hd) $stop;
	    if (outq != 10'h114) $stop;
	 end
	 if (cyc==7) begin
	    if (outr != 4'h4) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
