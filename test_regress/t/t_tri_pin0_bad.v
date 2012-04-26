// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   t_tri4 t_tri4 (.t4(1'b0));

endmodule

module t_tri4 (/*AUTOARG*/
   // Inputs
   t4
   );
   input t4;
   tri0  t4;
   initial if (t4 !== 1'b0) $stop;
endmodule
