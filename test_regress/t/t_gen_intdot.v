// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003-2006 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer 	cyc=0;

   wire 	out;
   reg 		in;
   
   Genit g (.clk(clk), .value(in), .result(out));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d %x %x\n",$time, cyc, in, out);
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 in <= 1'b1;
      end
      else if (cyc==1) begin
	 in <= 1'b0;
      end
      else if (cyc==2) begin
	 if (out != 1'b1) $stop;
      end
      else if (cyc==3) begin
	 if (out != 1'b0) $stop;
      end
      else if (cyc==9) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Generate (clk, value, result);
   input clk;
   input value;
   output result;

   reg Internal;

   assign result = Internal ^ clk;
  
   always @(posedge clk)
     Internal <= #1 value;
endmodule

module Checker (clk, value);
  input clk, value;

   always @(posedge clk) begin
      $write ("[%0t] value=%h\n", $time, value);
   end

endmodule

module Test (clk, value, result);
   input clk;
   input value;
   output result;

   Generate gen (clk, value, result);
   Checker  chk (clk, gen.Internal);

endmodule

module Genit (clk, value, result);
   input clk;
   input value;
   output result;

`define WITH_GENERATE
`ifdef WITH_GENERATE
   genvar i;
   generate
      for (i = 0; i < 1; i = i + 1)
	begin : gen
	   Test t (clk, value, result);
	end
   endgenerate
`else
   Test t (clk, value, result);
`endif
endmodule

