// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   value, value2
   );

   output reg [63:0] value;
   output wire [64:0] value2;

   assign value2 = {8'bx, 57'h12};

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
