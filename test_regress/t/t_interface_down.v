// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

interface ifc;
   integer value;
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );
`ifdef INLINE_A //verilator inline_module
`else  //verilator no_inline_module
`endif
   input clk;
   integer cyc=1;

   ifc itop1a();
   ifc itop1b();
   ifc itop2a();
   ifc itop2b();

   wrapper  c1 (.isuba(itop1a),
		.isubb(itop1b),
		.i_valuea(14),
		.i_valueb(15));
   wrapper  c2 (.isuba(itop2a),
		.isubb(itop2b),
		.i_valuea(24),
		.i_valueb(25));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
	 if (itop1a.value != 14) $stop;
	 if (itop1b.value != 15) $stop;
	 if (itop2a.value != 24) $stop;
	 if (itop2b.value != 25) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module wrapper
  (
   ifc isuba,
   ifc isubb,
   input integer i_valuea,
   input integer i_valueb
   );
`ifdef INLINE_B //verilator inline_module
`else  //verilator no_inline_module
`endif
   lower subsuba (.isub(isuba), .i_value(i_valuea));
   lower subsubb (.isub(isubb), .i_value(i_valueb));
endmodule

module lower
  (
   ifc isub,
   input integer i_value
   );
`ifdef INLINE_C //verilator inline_module
`else  //verilator no_inline_module
`endif
   always @* begin
      isub.value = i_value;
   end
endmodule
