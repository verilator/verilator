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

   integer i = 0;
   integer q[$] = {0, 1};

   always @(posedge clk) begin
      $display("%p", q[i:i+1]);
      q.push_back(i+2);
      i++;
      if (i >= 3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
