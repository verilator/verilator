// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   bar
   );

   wire  foo;
   output  bar;

   // Oh dear.
   assign  foo = bar;
   assign  bar = foo;

endmodule
