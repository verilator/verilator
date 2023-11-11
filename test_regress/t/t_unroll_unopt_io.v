// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   zeros,
   // Inputs
   num
   );

   parameter WIDTH = 1;
   input  logic [WIDTH-1:0] num;
   output logic [$clog2(WIDTH+1)-1:0] zeros;

   integer i;

   always_comb begin
      i = 0;
      while ((i < WIDTH) & ~num[WIDTH-1-i]) i = i + 1;
      zeros = i[$clog2(WIDTH+1) - 1 : 0];
   end

endmodule
