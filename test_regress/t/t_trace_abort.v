// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg [2:0] cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 3'd1;
      // Exit via abort to make sure trace is flushed
      if (&cyc) $stop;
   end

endmodule
