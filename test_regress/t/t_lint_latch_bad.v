// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   bl, cl, bc, cc,
   // Inputs
   a
   );

   input logic a;
   output logic bl;
   output logic cl;
   always_latch begin
      bl <= a;  // No warning
      cl = a;
   end

   output logic bc;
   output logic	cc;
   always_comb begin
      bc <= a;  // Warning
      cc = a;
   end


endmodule
