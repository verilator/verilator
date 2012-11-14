// DESCRIPTION: Verilator: Verilog Test module
//
// A test of the +verilog2001ext+ and +verilog2005ext+ flags.
//
// This source code uses the uwire declaration, which is only valid in Verilog
// 2005.
//
// Compile only test, so no need for "All Finished" output.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   uwire w;			// Only in Verilog 2005

endmodule
