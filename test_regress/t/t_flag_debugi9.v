// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   i
   );

   // Need some logic to get mtask debug fully covered
   input i;
   output wire o;
   assign o = i;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
