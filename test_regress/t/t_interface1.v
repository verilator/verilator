// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Very simple test for interface pathclearing

interface ifc;
   logic [3:0] value;
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc itop();

   sub  c1 (.isub(itop),
	    .i_value(4'h4));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
	 if (c1.i_value != 4) $stop;  // 'Normal' crossref just for comparison
	 if (itop.value != 4) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module sub
  (
   ifc isub,
   input logic [3:0] i_value
   );

   always @* begin
      isub.value = i_value;
   end
endmodule : sub
