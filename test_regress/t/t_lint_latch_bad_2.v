// DESCRIPTION: Verilator: Verilog Test module for issue #1609
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Julien Margetts
// SPDX-License-Identifier: Unlicense

module t (/*AUTOARG*/ a, b, o);
   input  a;
   input  b;
   output reg o;

   always_comb
     if (a)
       o = b;

endmodule
