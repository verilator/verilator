// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   reg [72:1] in;
   initial begin
      if (in[(   (1'h0 / 1'b0)   )+:71] != 71'h0) $stop;
   end

endmodule
