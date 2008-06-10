// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [11:0] in_a;
   reg [31:0] sel;
   wire [2:0] out_x;

   extractor #(4,3) extractor (
			       // Outputs
			       .out	(out_x),
			       // Inputs
			       .in	(in_a),
			       .sel	(sel));

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 //$write("%d %x %x %x\n", cyc, in_a, sel, out_x);
	 if (cyc==1) begin
	    in_a <= 12'b001_101_111_010;
	    sel <= 32'd0;
	 end
	 if (cyc==2) begin
	    sel <= 32'd1;
	    if (out_x != 3'b010) $stop;
	 end
	 if (cyc==3) begin
	    sel <= 32'd2;
	    if (out_x != 3'b111) $stop;
	 end
	 if (cyc==4) begin
	    sel <= 32'd3;
	    if (out_x != 3'b101) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule

module extractor (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in, sel
   );
   parameter IN_WIDTH=8;
   parameter OUT_WIDTH=2;

   input [IN_WIDTH*OUT_WIDTH-1:0] in;
   output [OUT_WIDTH-1:0]         out;
   input [31:0] 		  sel;

   wire [OUT_WIDTH-1:0] out = selector(in,sel);

   function [OUT_WIDTH-1:0] selector;
      input [IN_WIDTH*OUT_WIDTH-1:0] inv;
      input [31:0] 		  selv;
      integer i;
      begin
	 selector = 0;
	 for (i=0; i<OUT_WIDTH; i=i+1) begin
	    selector[i] = inv[selv*OUT_WIDTH+i];
	 end
      end
   endfunction
endmodule
