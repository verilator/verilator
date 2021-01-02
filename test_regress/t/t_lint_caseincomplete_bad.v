// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   i
   );

   input [1:0] i;

   always_comb begin
      case (i)
        2'b00: ;
        2'b10: ;
        2'b11: ;
      endcase
   end
endmodule
