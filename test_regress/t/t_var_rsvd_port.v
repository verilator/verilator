// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   bool
   );

   input bool;	// BAD

   reg  vector;	// OK, as not public
   reg  switch /*verilator public*/;	// Bad

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
