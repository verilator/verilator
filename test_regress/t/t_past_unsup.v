// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   d, clk, num
   );
   input d;
   input clk;
   input int num;

   always @ (posedge clk) begin
      if ($past(d, 1, 1)) $stop;  // Unsup
      if ($past(d, 1, 1, )) $stop;  // Unsup
      if ($past(d, 1, 1, @(posedge clk))) $stop;  // Unsup
   end
endmodule
