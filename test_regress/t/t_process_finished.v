// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
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
