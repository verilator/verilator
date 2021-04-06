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
      if ($past(d, num)) $stop;  // IEEE 16.9.3 must be const
      if ($past(d, 0)) $stop;  // IEEE 16.9.3 must be >= 0
      if ($past(d, 10000)) $stop;  // TICKCOUNT
   end
endmodule
