// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, increment
   );
   input clk;
   input [1:0] increment;

   typedef enum [3:0] {
                       E01 = 1,
                       E03 = 3,
                       E04 = 4,
                       E05 = 5
                       } my_t;

   my_t e;

   always @ (posedge clk) begin
      e.next(increment);
      $finish;
   end

endmodule
