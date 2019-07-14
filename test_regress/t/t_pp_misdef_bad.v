// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t;
`define DEFINED

   // NDEFINED isn't defined here:
   `NDEFINED

     // Botched directive (`timescale)
     `imescale

     initial $stop; // Should have failed

endmodule
