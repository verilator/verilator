// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Adrien Le Masle.
// SPDX-License-Identifier: CC0-1.0

package pack_a;
   parameter PARAM_A = 0;
endpackage : pack_a

//module t;
module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   parameter PARAM_A = 0;

   initial begin
      $display(PARAM_A);
      if (PARAM_A != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
