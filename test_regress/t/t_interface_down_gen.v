// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// This test demonstrates how not only parameters but the type of a parent
// interface could propagate down to child modules, changing their data type
// determinations.  Note presently unsupported in all commercial simulators.

interface ifc;
   parameter MODE = 0;
   generate
      // Note block must be named per SystemVerilog 2005
      if (MODE==1) begin : g
	 integer value;
      end
      else if (MODE==2) begin : g
	 real value;
      end
   endgenerate
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc #(1) itop1a();
   ifc #(1) itop1b();
   ifc #(2) itop2a();
   ifc #(2) itop2b();

   wrapper  c1 (.isuba(itop1a),
		.isubb(itop1b),
		.i_valuea(14.1),
		.i_valueb(15.2));
   wrapper  c2 (.isuba(itop2a),
		.isubb(itop2b),
		.i_valuea(24.3),
		.i_valueb(25.4));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
	 if (itop1a.g.value != 14) $stop;
	 if (itop1b.g.value != 15) $stop;
	 if (itop2a.g.value != 24) $stop;
	 if (itop2b.g.value != 25) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module wrapper
  (
   ifc isuba,
   ifc isubb,
   input real i_valuea,
   input real i_valueb
   );
   lower subsuba (.isub(isuba), .i_value(i_valuea));
   lower subsubb (.isub(isubb), .i_value(i_valueb));
endmodule

module lower
  (
   ifc isub,
   input real i_value
   );
   always @* begin
`error Commercial sims choke on cross ref here
      isub.g.value = i_value;
   end
endmodule
