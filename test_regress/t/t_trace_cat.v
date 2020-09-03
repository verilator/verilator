// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   input wire clk
   );

   integer    cyc; initial cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
   end
endmodule
