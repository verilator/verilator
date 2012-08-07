// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   parameter PAR = 3;

   wire [31:0] o1a,o1b;

   m1 #(0) m1a(.o(o1a));
   m1 #(1) m1b(.o(o1b));

   always @ (posedge clk) begin
      if (o1a != 8) $stop;
      if (o1b != 4) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module m1 (output wire [31:0] o);
   parameter W = 0;
   generate
      if (W == 0) begin
         m2 m2 (.o(o));
	 defparam m2.PAR2 = 8;
      end
      else begin
         m2 m2 (.o(o));
	 defparam m2.PAR2 = 4;
      end
   endgenerate
endmodule

module m2 (output wire [31:0] o);
   parameter PAR2 = 10;
   assign o = PAR2;
endmodule
