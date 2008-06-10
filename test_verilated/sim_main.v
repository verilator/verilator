// DESCRIPTION: Verilator Test: Top level main for invoking model
//
// Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.

module sim_main;
   /*verilator public_module*/

   reg  clk;
   reg  check;
   wire done;

   vgen vgen (/*AUTOINST*/
	      // Outputs
	      .done			(done),
	      // Inputs
	      .clk			(clk),
	      .check			(check));

   integer i;

   initial begin
      check = 1'b0;
      clk = 1'b0;
      for (i=0; i<10*vgen.CYCLES; i=i+1) begin
	 #5;
	 clk = ~clk;
	 #5;
	 clk = ~clk;
      end
      check = 1'b1;
      for (i=0; i<10; i=i+1) begin
	 #5;
	 clk = ~clk;
	 #5;
	 clk = ~clk;
      end
   end

endmodule
