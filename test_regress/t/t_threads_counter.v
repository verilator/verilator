// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2017 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int cyc;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc!=0) begin
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule
