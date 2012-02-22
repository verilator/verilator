// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2012 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   genvar g;
   logic [1:0] mask = 0;
   generate
      for (g=0; g<2; g++)
	begin : picker
	   logic block_passed = 0;  // Just for visualizing V3LinkDot debug
	   function [3:0] pick;
	      input [3:0]      randnum;
	      pick = randnum+g[3:0];
	   endfunction
	   always @(posedge clk) begin
	      if (pick(3)!=3+g[3:0]) $stop;
	      else mask[g] = 1'b1;
	      if (mask == 2'b11) begin  // All iterations must be finished
		 $write("*-* All Finished *-*\n");
		 $finish;
	      end
	   end
	end
   endgenerate
endmodule
