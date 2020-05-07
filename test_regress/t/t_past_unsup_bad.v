// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (d, clk);
   input d;
   input clk;

   always @ (posedge clk) begin
      // Unsupported
      if ($past(d, 0, 0, 0)) $stop;
   end
endmodule
