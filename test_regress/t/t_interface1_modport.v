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
	    .i_value(cyc));

   sub2 c2 (.isub2(itop),
	    .i_value(cyc));

   always @(*) itop.hidden_from_isub = cyc + 1;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
	 if (itop.value != 20) $stop;
	 if (itop.hidden_from_isub != 21) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module sub2
  (
   ifc.out_modport isub2,
   input integer i_value
   );

   sub  c3 (.isub(isub2),
	    .i_value(i_value));
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
