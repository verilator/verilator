// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub;
   integer i;
   initial begin
      i = 23.2;
      i = 23.0; // No warning - often happens with units of time
   end
endmodule
