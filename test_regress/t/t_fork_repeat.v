// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   bit clk;

   // Gen Clock
   always #10
     clk = ~clk;

   initial begin
      fork
         begin
            forever
              @(posedge clk);
         end
         begin
            repeat(10)
              @(posedge clk);
         end
         begin
            for(int i=0; i < 6; ++i)
              @(posedge clk);
         end
      join_any

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
