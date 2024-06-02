// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t();
   logic clk = 0;
   logic out = 1;

   always #5 clk = ~clk;

   initial begin
      while(1) begin
         if(out) begin
            break;
         end
         @(negedge clk);
      end

      $write("*-* All Finished *-*\n");
      $finish();
   end
endmodule
