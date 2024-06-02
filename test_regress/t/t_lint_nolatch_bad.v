// DESCRIPTION: Verilator: Verilog Test module for issue #1609
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Julien Margetts.
// SPDX-License-Identifier: Unlicense

module t (/*AUTOARG*/ a, b, o);
   input  a;
   input  b;
   output reg o;

   always_latch
     if (a)
       o = b;
     else
       o = ~b;

endmodule
