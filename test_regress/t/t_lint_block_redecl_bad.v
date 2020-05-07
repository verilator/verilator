// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug485, but see t_gen_forif.v for an OK example.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   always_comb begin
      integer i;

      for(i=0; i<10; i++ ) begin: COMB
      end

      for(i=0; i<9; i++ ) begin: COMB
      end
   end
endmodule
