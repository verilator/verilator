// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   looped looped ();

endmodule

module looped (/*AUTOARG*/);
   looped2 looped2 ();
endmodule

module looped2 (/*AUTOARG*/);
   looped looped ();
endmodule
