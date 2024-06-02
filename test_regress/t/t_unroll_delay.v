// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   integer i;
   integer j;

   always @(i, j) $display("[%0t] B %0d %0d", $time, i, j);

   // See issue #4237

   initial begin
      for(i = 1; i < 3 ; i = i + 1) begin
         $display("");
         for(j = 6; j < 8; j = j + 1) begin
            $display("[%0t] A %0d %0d", $time, i, j);
            #1;
            $display("[%0t] C %0d %0d", $time, i, j);
         end
         #9;
      end
      #10;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
