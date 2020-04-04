// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   tri [3:0] w;

   pullup p0 (w[0]);
   pulldown p1 (w[1]);
   pulldown p2 (w[2]);
   pullup p3 (w[3]);

   always_ff @ (posedge clk) begin
      if (w != 4'b1001) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
