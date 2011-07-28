// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

import "DPI-C" context function integer mon_check();

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg		onebit		/*verilator public_flat_rw @(posedge clk) */;
   reg [2:1]	twoone		/*verilator public_flat_rw @(posedge clk) */;
   reg [4:3][2:1] fourthreetwoone /*verilator public_flat_rw @(posedge clk) */;

   reg [3:2][61:0] quads	/*verilator public_flat_rw @(posedge clk) */;

   reg [31:0] 	   count	/*verilator public_flat_rd */;
   reg [31:0] 	   half_count	/*verilator public_flat_rd */;
   
   integer 	  status;

   sub sub();

   // Test loop
   initial begin
      onebit = 1'b0;
      status = mon_check();
      if (status!=0) begin
	 $write("%%Error: t_vpi_var.cpp:%0d: C Test failed\n", status);
	 $stop;
      end
      if (onebit != 1'b1) $stop;
      if (quads[2] != 62'h12819213_abd31a1c) $stop;
      if (quads[3] != 62'h1c77bb9b_3784ea09) $stop;
   end

   always @(posedge clk) begin
      count <= count + 2;
      if (count[1])
	half_count <= half_count + 2;

      if (count == 1000) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module sub;
   reg subsig1 /*verilator public_flat_rd*/;
   reg subsig2 /*verilator public_flat_rd*/;
endmodule
