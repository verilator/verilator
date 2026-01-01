// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic [7:0]  i1 [8],
    input logic [7:0]  i2 [16],
    input logic [7:0]  i3 [512],
    output logic [7:0] o1 [8],
    output logic [7:0]  o2 [16],
    output logic [7:0] o3 [256]
   );

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
