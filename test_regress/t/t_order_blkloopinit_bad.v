// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   clk
   );
   input clk;
   output int o;

   localparam SIZE = 65536;
   int array [SIZE];

   always @ (posedge clk) begin
      for (int i=0; i<SIZE; i++) begin
         array[i] <= 0;  // BLKLOOPINIT
      end
      o <= array[1];
   end

endmodule
