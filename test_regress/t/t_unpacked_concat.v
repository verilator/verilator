// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   typedef int ai3_t[1:3];
   ai3_t a3;
   int a9[1:9];

   logic [2:0] s0;
   logic [2:0] s1[1:3];
   logic [2:0] s1b[3:1];
   logic [2:0] s3[2:8];
   logic [2:0] s3b[8:2];

   initial begin
      s0 = 3'd1;
      s1[1] = 3'd2;
      s1[2] = 3'd3;
      s1[3] = 3'd4;
      s1b[1] = 3'd5;
      s1b[2] = 3'd6;
      s1b[3] = 3'd7;

      a3 = '{1, 2, 3};
      a9 = {a3, 4, 5, a3, 6};
      if (a9[1] != 1) $stop;
      if (a9[2] != 2) $stop;
      if (a9[3] != 3) $stop;
      if (a9[4] != 4) $stop;
      if (a9[5] != 5) $stop;
      if (a9[6] != 1) $stop;
      if (a9[7] != 2) $stop;
      if (a9[8] != 3) $stop;
      if (a9[9] != 6) $stop;

      s3 = {s0, s1, s1b};
      if (s3[2] != s0) $stop;
      if (s3[3] != s1[1]) $stop;
      if (s3[4] != s1[2]) $stop;
      if (s3[5] != s1[3]) $stop;
      if (s3[6] != s1b[3]) $stop;
      if (s3[7] != s1b[2]) $stop;
      if (s3[8] != s1b[1]) $stop;

      s3[2:8] = {s0, s1[1:2], s1[3], s1b[3], s1b[2:1]};
      if (s3[2] != s0) $stop;
      if (s3[3] != s1[1]) $stop;
      if (s3[4] != s1[2]) $stop;
      if (s3[5] != s1[3]) $stop;
      if (s3[6] != s1b[3]) $stop;
      if (s3[7] != s1b[2]) $stop;
      if (s3[8] != s1b[1]) $stop;

      s3 = {s0, s1[1], s1[2:3], s1b[3:2], s1b[1]};
      if (s3[2] != s0) $stop;
      if (s3[3] != s1[1]) $stop;
      if (s3[4] != s1[2]) $stop;
      if (s3[5] != s1[3]) $stop;
      if (s3[6] != s1b[3]) $stop;
      if (s3[7] != s1b[2]) $stop;
      if (s3[8] != s1b[1]) $stop;

      s3b = {s0, s1, s1b};
      if (s3b[8] != s0) $stop;
      if (s3b[7] != s1[1]) $stop;
      if (s3b[6] != s1[2]) $stop;
      if (s3b[5] != s1[3]) $stop;
      if (s3b[4] != s1b[3]) $stop;
      if (s3b[3] != s1b[2]) $stop;
      if (s3b[2] != s1b[1]) $stop;

      s3b[8:2] = {s0, s1[1:2], s1[3], s1b[3], s1b[2:1]};
      if (s3b[8] != s0) $stop;
      if (s3b[7] != s1[1]) $stop;
      if (s3b[6] != s1[2]) $stop;
      if (s3b[5] != s1[3]) $stop;
      if (s3b[4] != s1b[3]) $stop;
      if (s3b[3] != s1b[2]) $stop;
      if (s3b[2] != s1b[1]) $stop;

      s3b = {s0, s1[1], s1[2:3], s1b[3:2], s1b[1]};
      if (s3b[8] != s0) $stop;
      if (s3b[7] != s1[1]) $stop;
      if (s3b[6] != s1[2]) $stop;
      if (s3b[5] != s1[3]) $stop;
      if (s3b[4] != s1b[3]) $stop;
      if (s3b[3] != s1b[2]) $stop;
      if (s3b[2] != s1b[1]) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
