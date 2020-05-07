// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

function automatic integer min(input integer a, input integer b);
   return (a < b) ? a : b;
endfunction

module t
  #(parameter A=16, parameter B=8)
   (/*AUTOARG*/
   // Outputs
   c,
   // Inputs
   a, b
   );

   input [A-1:0] a;
   input [B-1:0] b;
   output logic [min(A,B)-1:0] c;

   always_comb
     for (int i = 0; i < min(A,B); i++)
       assign c[i] = a[i] | b[i];

endmodule
