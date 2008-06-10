// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t;
`define A B

   // NOTDEF isn't defined here:
   `NOTDEF

//`include "notfound"

     initial $stop; // Should have failed

endmodule
