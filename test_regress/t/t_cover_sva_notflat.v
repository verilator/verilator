// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg 	 toggle;
   integer cyc; initial cyc=1;

   Test suba (/*AUTOINST*/
	      // Inputs
	      .clk			(clk),
	      .toggle			(toggle),
	      .cyc			(cyc[31:0]));
   Test subb (/*AUTOINST*/
	      // Inputs
	      .clk			(clk),
	      .toggle			(toggle),
	      .cyc			(cyc[31:0]));
   Test subc (/*AUTOINST*/
	      // Inputs
	      .clk			(clk),
	      .toggle			(toggle),
	      .cyc			(cyc[31:0]));

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 toggle <= !cyc[0];
	 if (cyc==9) begin
	 end
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module Test
  (
   input clk,
   input toggle,
   input [31:0] cyc
   );

   // Don't flatten out these modules please:
   // verilator no_inline_module

   // Labeled cover
   cyc_eq_5: cover property (@(posedge clk) cyc==5) $display("*COVER: Cyc==5");

endmodule
