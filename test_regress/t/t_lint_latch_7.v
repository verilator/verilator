// DESCRIPTION: Verilator: Verilog Test module for Issue#xxxx
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Julien Margetts
// SPDX-License-Identifier: Unlicense

module test #(parameter W = 65)
  (input  logic [W-1:0] a,
   input  logic              e,
   output logic [W-1:0] z);

   integer i;

   always @(*)
       if (e)
           for (i=0;i<W;i=i+1)
               z[i] = a[i];
       else
           z = W'(0);

endmodule
