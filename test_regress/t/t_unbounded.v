// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t();

   localparam UNB = $;
   localparam int UNB2 = $;
   localparam SIX = 6;

   initial begin
      if ($bits($isunbounded(0)) !== 1) $stop;
      if ($isunbounded(0) !== 1'b0) $stop;
      if ($isunbounded(SIX) !== 0) $stop;
      if ($isunbounded($) !== 1) $stop;
      if ($isunbounded(UNB) !== 1) $stop;
      if ($isunbounded(UNB2) !== 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
