// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

interface ifc;
   integer ok;
   integer bad;
   modport out_modport (output ok);
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc itop();

   counter_ansi  c1 (.isub(itop),
		     .i_value(4'h4));

endmodule

module counter_ansi
  (
   ifc.out_modport isub,
   input logic [3:0] i_value
   );

   always @* begin
      isub.ok = i_value;
      isub.bad = i_value;  // Illegal access
   end
endmodule
