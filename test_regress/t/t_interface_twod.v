// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

interface ifc;
   integer value;
   modport i (output value);
   modport o (input value);
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer cyc=1;

   ifc itop1a(),
       itop1b();

   wrapper  c1 (.isuba(itop1a),
		.isubb(itop1b),
		.i_valuea(14),
		.i_valueb(15));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
	 if (itop1a.value != 14) $stop;
	 if (itop1b.value != 15) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module wrapper
  (
   ifc.i isuba, isubb,
   input integer i_valuea, i_valueb
   );
   always @* begin
      isuba.value = i_valuea;
      isubb.value = i_valueb;
   end
endmodule
