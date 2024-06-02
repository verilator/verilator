// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   /* verilator tracing_off */

   input clk;

   reg [7:0] cyc = 8'd0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
