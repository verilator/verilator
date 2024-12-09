// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic [255:0] arrd [0:0] = '{ 1 };
   logic [255:0] y0;

   // Do not exclude from inlining wide arraysels.
   always_comb y0 = arrd[0];

   always_comb begin
     if (y0 != 1 && y0 != 0) begin
       $stop;
     end
   end
endmodule
