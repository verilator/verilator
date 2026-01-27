// DESCRIPTION: Verilator: Verilog Test module for Issue#xxxx
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Julien Margetts
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
