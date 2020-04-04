// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug789 generates

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc #(1) itopa();
   ifc #(2) itopb();

   sub #(1) ca (.isub(itopa),
		.i_value(4));
   sub #(2) cb (.isub(itopb),
		.i_value(5));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==1) begin
	 if (itopa.MODE != 1) $stop;
	 if (itopb.MODE != 2) $stop;
      end
      if (cyc==20) begin
	 if (itopa.i != 4) $stop;
	 if (itopb.i != 5) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module sub
  #(parameter MODE = 0)
   (
    ifc isub,
    input integer i_value
   );

   // Commercial unsupported Xmrs into scopes within interfaces
   generate
      always_comb isub.i = i_value;
   endgenerate
endmodule

interface ifc;
   parameter MODE = 0;
   // Commercial unsupported Xmrs into scopes within interfaces
   generate
      integer 	  i;
   endgenerate
endinterface
