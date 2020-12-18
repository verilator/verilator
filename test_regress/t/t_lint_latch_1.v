// DESCRIPTION: Verilator: Verilog Test module for Issue#1609
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Julien Margetts.

module t (/*AUTOARG*/ a, b, o);
   input  a;
   input  b;
   output reg o;

   // verilator lint_off LATCH
   always @(a or b)
     if (a)
       o <= b;

endmodule
