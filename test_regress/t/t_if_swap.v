// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer f;

   always @(posedge clk) begin
      if (!$feof(f)) begin
         $display("Doing stuff with file.");
      end
      // Commenting out these two lines fixes the fault
      else begin
      end
      if (!$feof(f)) begin
      end
      else begin
         $display("Not doing stuff with file.");
      end
   end

endmodule
