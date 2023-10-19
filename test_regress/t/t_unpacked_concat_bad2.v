// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic [7:0] s0;
   logic [7:0] s1[1:2];
   logic [7:0] s2[1:4];
   logic [7:0] s3[2][2];

   typedef int AI3[1:3];
   AI3 A3;
   logic [31:0] A9_logic[1:9];

   initial begin
      // RHS has too many elements.
      s1 = {s0, s2};
      s2 = {s1, s0, s0, s0};
      // Incompatible type
      s2 = {s0, s3};

      A9_logic = {A3, 4, 5, A3, 6};
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
