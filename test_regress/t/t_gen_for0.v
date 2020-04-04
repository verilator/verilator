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

   integer 	cyc=0;

   Testit testit (/*AUTOINST*/
		  // Inputs
		  .clk			(clk));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
      end
      else if (cyc<10) begin
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Testit (clk);
   input clk;

   genvar igen;
   generate
      for (igen=0; igen<0; igen=igen+1) begin : test_gen
	 always @ (posedge clk) begin
	    $display("igen1 = %d", igen);
	    $stop;
	 end
      end
   endgenerate

endmodule
