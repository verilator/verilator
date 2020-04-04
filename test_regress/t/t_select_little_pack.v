// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // No endian warning here
   reg [7:0] pack [3:0];

   initial begin
      pack[0] = 8'h78;
      pack[1] = 8'h88;
      pack[2] = 8'h98;
      pack[3] = 8'hA8;
      if (pack[0] !== 8'h78) $stop;
      if (pack[1] !== 8'h88) $stop;
      if (pack[2] !== 8'h98) $stop;
      if (pack[3] !== 8'hA8) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
