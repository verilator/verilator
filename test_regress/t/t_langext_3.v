// DESCRIPTION: Verilator: Verilog Test module
//
// A test of the +verilog2001ext+ and +verilog2005ext+ flags.
//
// This source code uses the uwire declaration, which is only valid in Verilog
// 2005.
//
// Compile only test, so no need for "All Finished" output.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Jeremy Bennett
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   uwire w;  // Only in Verilog 2005

endmodule
