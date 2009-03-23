// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc = 0;

   covlabel:
     cover property (@(posedge clk) cyc==5);
   covlabel:  // Error: Duplicate block_identifier
     cover property (@(posedge clk) cyc==5);

endmodule
