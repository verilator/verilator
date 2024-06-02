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

   typedef int AI3[1:3];
   AI3 A3;
   int A9[1:9];

   logic [2:0] s0;
   logic [2:0] s1[1:3];
   logic [2:0] s2[3:1];
   logic [2:0] s3[2:8];
   logic [2:0] s4[8:2];

   initial begin
      s0 = 3'd1;
      s1[1] = 3'd2;
      s1[2] = 3'd3;
      s1[3] = 3'd4;
      s2[1] = 3'd5;
      s2[2] = 3'd6;
      s2[3] = 3'd7;

      A3 = '{1, 2, 3};
      A9 = {A3, 4, 5, A3, 6};
      if (A9[1] != 1) $stop;
      if (A9[2] != 2) $stop;
      if (A9[3] != 3) $stop;
      if (A9[4] != 4) $stop;
      if (A9[5] != 5) $stop;
      if (A9[6] != 1) $stop;
      if (A9[7] != 2) $stop;
      if (A9[8] != 3) $stop;
      if (A9[9] != 6) $stop;

      s3 = {s0, s1, s2};
      if (s3[2] != s0) $stop;
      if (s3[3] != s1[1]) $stop;
      if (s3[4] != s1[2]) $stop;
      if (s3[5] != s1[3]) $stop;
      if (s3[6] != s2[3]) $stop;
      if (s3[7] != s2[2]) $stop;
      if (s3[8] != s2[1]) $stop;

      s3[2:8] = {s0, s1[1:2], s1[3], s2[3], s2[2:1]};
      if (s3[2] != s0) $stop;
      if (s3[3] != s1[1]) $stop;
      if (s3[4] != s1[2]) $stop;
      if (s3[5] != s1[3]) $stop;
      if (s3[6] != s2[3]) $stop;
      if (s3[7] != s2[2]) $stop;
      if (s3[8] != s2[1]) $stop;

      s3 = {s0, s1[1], s1[2:3], s2[3:2], s2[1]};
      if (s3[2] != s0) $stop;
      if (s3[3] != s1[1]) $stop;
      if (s3[4] != s1[2]) $stop;
      if (s3[5] != s1[3]) $stop;
      if (s3[6] != s2[3]) $stop;
      if (s3[7] != s2[2]) $stop;
      if (s3[8] != s2[1]) $stop;

      s4 = {s0, s1, s2};
      if (s4[8] != s0) $stop;
      if (s4[7] != s1[1]) $stop;
      if (s4[6] != s1[2]) $stop;
      if (s4[5] != s1[3]) $stop;
      if (s4[4] != s2[3]) $stop;
      if (s4[3] != s2[2]) $stop;
      if (s4[2] != s2[1]) $stop;

      s4[8:2] = {s0, s1[1:2], s1[3], s2[3], s2[2:1]};
      if (s4[8] != s0) $stop;
      if (s4[7] != s1[1]) $stop;
      if (s4[6] != s1[2]) $stop;
      if (s4[5] != s1[3]) $stop;
      if (s4[4] != s2[3]) $stop;
      if (s4[3] != s2[2]) $stop;
      if (s4[2] != s2[1]) $stop;

      s4 = {s0, s1[1], s1[2:3], s2[3:2], s2[1]};
      if (s4[8] != s0) $stop;
      if (s4[7] != s1[1]) $stop;
      if (s4[6] != s1[2]) $stop;
      if (s4[5] != s1[3]) $stop;
      if (s4[4] != s2[3]) $stop;
      if (s4[3] != s2[2]) $stop;
      if (s4[2] != s2[1]) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
