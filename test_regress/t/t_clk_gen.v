// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   // verilator lint_off GENCLK
   reg 	      gendlyclk_r;
   reg [31:0] gendlydata_r;
   reg [31:0] dlydata_gr;

   reg 	      genblkclk;
   reg [31:0] genblkdata;
   reg [31:0] blkdata_gr;

   wire [31:0] constwire = 32'h11;
   reg [31:0]  initwire;

   integer     i;
   initial begin
      for (i=0; i<10000; i=i+1) begin
	 initwire = 32'h2200;
      end
   end

   wire [31:0] either        = gendlydata_r | dlydata_gr | blkdata_gr | initwire | constwire;
   wire [31:0] either_unused = gendlydata_r | dlydata_gr | blkdata_gr | initwire | constwire;

   always @ (posedge clk) begin
      gendlydata_r <= 32'h0011_0000;
      gendlyclk_r <= 0;
      // surefire lint_off SEQASS
      genblkclk  = 0;
      genblkdata = 0;
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==2) begin
	    gendlyclk_r <= 1;
	    gendlydata_r <= 32'h00540000;
	    genblkclk = 1;
	    genblkdata = 32'hace;
	    $write("[%0t] Send pulse\n", $time);
	 end
	 if (cyc==3) begin
	    genblkdata = 32'hdce;
	    gendlydata_r <= 32'h00ff0000;
	    if (either != 32'h87542211) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
      // surefire lint_on SEQASS
   end

   always @ (posedge gendlyclk_r) begin
      if ($time>0) begin	// Hack, don't split the block
	 $write("[%0t] Got gendlyclk_r, d=%x b=%x\n", $time, gendlydata_r, genblkdata);
	 dlydata_gr <= 32'h80000000;
	 // Delayed activity list will already be completed for gendlydata
	 // because genclk is from a delayed assignment.
	 // Thus we get the NEW not old value of gendlydata_r
	 if (gendlydata_r != 32'h00540000) $stop;
	 if (genblkdata != 32'hace) $stop;
      end
   end

   always @ (posedge genblkclk) begin
      if ($time>0) begin	// Hack, don't split the block
	 $write("[%0t] Got genblkclk, d=%x b=%x\n", $time, gendlydata_r, genblkdata);
	 blkdata_gr <= 32'h07000000;
	 // Clock from non-delayed assignment, we get old value of gendlydata_r
`ifdef verilator `else	// V3.2 races... technically legal
	 if (gendlydata_r != 32'h00110000) $stop;
`endif
	 if (genblkdata != 32'hace) $stop;
      end
   end

endmodule
