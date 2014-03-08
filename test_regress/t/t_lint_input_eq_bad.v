// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t
   (
   input wire i,
   input wire i2 = i   // BAD
   );

endmodule
