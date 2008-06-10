// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/);

   wire  foo;
   wire  bar;

   // Oh dear.
   assign  foo = bar;
   assign  bar = foo;

endmodule
