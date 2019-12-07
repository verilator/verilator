// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

// Very simple test for interface pathclearing

interface ifc;
   integer hidden_from_isub;
   integer value;
   modport out_modport (output value);
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc itop();

   sub  c1 (.isub(itop),
	    .i_value(4));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
	 if (itop.value != 4) $stop;
	 itop.hidden_from_isub = 20;
	 if (itop.hidden_from_isub != 20) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module sub
`ifdef NANSI  // bug868
  (
   isub, i_value
   );
   ifc.out_modport isub;   // Note parenthesis are not legal here
   input integer i_value;
`else
  (
   ifc.out_modport isub,
   input integer i_value
   );
`endif

   always @* begin
      isub.value = i_value;
   end
endmodule
