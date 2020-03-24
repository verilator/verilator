// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   secret i_secred(.clk(clk));

endmodule
