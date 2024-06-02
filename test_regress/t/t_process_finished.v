// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   process p;

   initial begin
      p = process::self();
   end

   always @(posedge clk) begin
      if (p.status() != process::FINISHED)
         $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
