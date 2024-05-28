// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);

   integer a1 [][];
   integer a2 [2][];

   integer a3 [][] = '{'{1, 2, 3}, '{4, 5, 6}};
   integer a4 [][] = '{{7, 8, 9}, {10, 11, 12}};
   integer a5 [][] = '{3{'{13, 14}}};

   integer aa1 [string][];
   integer wa1 [*][];
   integer qa1 [$][];
   struct {
      integer i;
      integer a[];
   } s1;

   integer a[] = '{1,2,3};

   logic [7:0][3:0] a6 [][];

   initial begin
      `checkh(a1.size, 0);
      a1 = new [3];
      `checkh(a1.size, 3);
      `checkh($size(a1), 3);
      `checkh($high(a1), 2);
      `checkh($right(a1), 2);

      foreach (a1[i]) a1[i] = new [i + 1];

      foreach (a1[i]) begin
         `checkh(a1[i].size, i + 1);
         `checkh($size(a1[i]), i + 1);
         `checkh($high(a1[i]), i);
         `checkh($right(a1[i]), i);
      end

      foreach (a1[i, j]) a1[i][j] = i * 10 + j;

      `checkh(a1[0][0], 0);
      `checkh(a1[1][0], 10);
      `checkh(a1[1][1], 11);
      `checkh(a1[2][0], 20);
      `checkh(a1[2][1], 21);
      `checkh(a1[2][2], 22);

      `checkh(a1[2].sum, 63);

      foreach (a1[i]) a1[i].delete;
      foreach (a1[i]) begin
         `checkh(a1[i].size, 0);
      end

      a1.delete;
      `checkh(a1.size, 0);

      a1 = new [2];
      `checkh(a1.size, 2);

      foreach (a1[i]) a1[i] = new [i + 2];
      foreach (a1[i]) begin
         `checkh(a1[i].size, i + 2);
      end

      foreach (a2[i]) begin
         `checkh(a2[i].size, 0);
      end
      foreach (a2[i]) a2[i] = new [i + 1];
      foreach (a2[i]) begin
         `checkh(a2[i].size, i + 1);
      end

      foreach (a2[i]) a2[i].delete;
      foreach (a2[i]) begin
         `checkh(a2[i].size, 0);
      end

      `checkh(a3.size, 2);
      foreach (a3[i]) begin
         `checkh(a3[i].size, 3);
      end

      `checkh(a3[0][0], 1);
      `checkh(a3[0][1], 2);
      `checkh(a3[0][2], 3);
      `checkh(a3[1][0], 4);
      `checkh(a3[1][1], 5);
      `checkh(a3[1][2], 6);

      `checkh(a4.size, 2);
      foreach (a4[i]) begin
         `checkh(a4[i].size, 3);
      end

      `checkh(a4[0][0], 7);
      `checkh(a4[0][1], 8);
      `checkh(a4[0][2], 9);
      `checkh(a4[1][0], 10);
      `checkh(a4[1][1], 11);
      `checkh(a4[1][2], 12);

      `checkh(a5.size, 3);
      foreach (a5[i]) begin
         `checkh(a5[i].size, 2);
      end

      `checkh(a5[0][0], 13);
      `checkh(a5[0][1], 14);
      `checkh(a5[1][0], 13);
      `checkh(a5[1][1], 14);
      `checkh(a5[2][0], 13);
      `checkh(a5[2][1], 14);

      a5 = a4;
      `checkh(a5.size, 2);
      foreach (a5[i]) begin
         `checkh(a5[i].size, 3);
      end

      `checkh(a5[0][0], 7);
      `checkh(a5[0][1], 8);
      `checkh(a5[0][2], 9);
      `checkh(a5[1][0], 10);
      `checkh(a5[1][1], 11);
      `checkh(a5[1][2], 12);

      a4 = '{'{15, 16}, '{17, 18}};

      `checkh(a4.size, 2);
      foreach (a4[i]) begin
         `checkh(a4[i].size, 2);
      end

      `checkh(a4[0][0], 15);
      `checkh(a4[0][1], 16);
      `checkh(a4[1][0], 17);
      `checkh(a4[1][1], 18);

      a4 = '{{19}, {20}, {21, 22}};

      `checkh(a4.size, 3);
      `checkh(a4[0].size, 1);
      `checkh(a4[1].size, 1);
      `checkh(a4[2].size, 2);

      `checkh(a4[0][0], 19);
      `checkh(a4[1][0], 20);
      `checkh(a4[2][0], 21);
      `checkh(a4[2][1], 22);

      a5 = '{2{a}};

      `checkh(a5.size, 2);
      foreach (a5[i]) begin
         `checkh(a5[i].size, 3);
      end

      `checkh(a5[0][0], 1);
      `checkh(a5[0][1], 2);
      `checkh(a5[0][2], 3);
      `checkh(a5[1][0], 1);
      `checkh(a5[1][1], 2);
      `checkh(a5[1][2], 3);

      a5 = '{};
      `checkh(a5.size, 0);

      a5 = '{2{'{}}};

      `checkh(a5.size, 2);
      foreach (a5[i]) begin
         `checkh(a5[i].size, 0);
      end

      aa1["k1"] = new [3];
      `checkh(aa1["k1"].size, 3);
      aa1["k1"].delete;

      wa1[1] = new [3];
      `checkh(wa1[1].size, 3);
      wa1[1].delete;

      qa1.push_back(a);
      `checkh(qa1[0].size, 3);
      qa1[0] = new [4];
      `checkh(qa1[0].size, 4);
      qa1[0].delete;

      s1.a = new [4];
      `checkh(s1.a.size, 4);
      s1.a.delete;

      `checkh($dimensions(a1), 3);
      `checkh($dimensions(a2), 3);
      `checkh($dimensions(aa1), 3);
      `checkh($dimensions(wa1), 3);
      `checkh($dimensions(qa1), 3);
      `checkh($dimensions(a), 2);
      `checkh($dimensions(a6), 4);
      `checkh($unpacked_dimensions(a1), 2);
      `checkh($unpacked_dimensions(a2), 2);
      `checkh($unpacked_dimensions(aa1), 2);
      `checkh($unpacked_dimensions(wa1), 2);
      `checkh($unpacked_dimensions(qa1), 2);
      `checkh($unpacked_dimensions(a), 1);
      `checkh($unpacked_dimensions(a6), 2);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
