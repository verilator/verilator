// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  typedef int ai3_t[1:3];
  typedef enum logic [1:0] {
    E0,
    E1,
    E2
  } enum_t;
  ai3_t a3;
  int a9[1:9];

  logic [2:0] s0;
  logic [2:0] s1[1:3];
  logic [2:0] s1b[3:1];
  logic [2:0] s3[2:8];
  logic [2:0] s3b[8:2];

  // Arrays spliced into concatenations evaluated as constants
  function automatic int f_spliced(int k);
    int a[2];
    int b[4];
    a = '{1, 2};
    b = {a, 5, 6};
    return b[k];
  endfunction
  typedef int a2_t[2];
  function automatic a2_t f_pair();
    return '{1, 2};
  endfunction

  initial begin
    begin
      localparam int L0 = f_spliced(0);
      localparam int L1 = f_spliced(1);
      localparam int L2 = f_spliced(2);
      localparam int L3 = f_spliced(3);
      localparam int P[4] = {f_pair(), 7, 8};
      `checkd(L0, 1);
      `checkd(L1, 2);
      `checkd(L2, 5);
      `checkd(L3, 6);
      `checkd(P[0], 1);
      `checkd(P[1], 2);
      `checkd(P[2], 7);
      `checkd(P[3], 8);
    end
    begin  // A constant array value spliced in
      int x3[3];
      x3 = {a2_t'{1, 2}, 3};
      `checkd(x3[0], 1);
      `checkd(x3[1], 2);
      `checkd(x3[2], 3);
    end
    begin  // Arrays spliced in, of elements that are themselves arrays
      logic [7:0] e[2:0];
      logic [7:0] e3[3:1][2:0];
      logic [7:0] e4[3:0][2:0];
      logic [7:0] e5[4:0][2:0];
      foreach (e[j]) e[j] = 8'(100 + j);
      foreach (e4[i, j]) e4[i][j] = 8'(i * 3 + j);
      e3[3:1] = {e4[1:0], e};
      foreach (e[j]) begin
        `checkd(e3[3][j], e4[1][j]);
        `checkd(e3[2][j], e4[0][j]);
        `checkd(e3[1][j], e[j]);
      end
      e5 = {e, e4};
      foreach (e[j]) begin
        `checkd(e5[4][j], e[j]);
        `checkd(e5[3][j], e4[3][j]);
        `checkd(e5[2][j], e4[2][j]);
        `checkd(e5[1][j], e4[1][j]);
        `checkd(e5[0][j], e4[0][j]);
      end
    end
    begin  // An array of enums spliced in
      enum_t en2[2];
      enum_t en3[3];
      en2 = '{E1, E2};
      en3 = {en2, E0};
      `checkd(en3[0], E1);
      `checkd(en3[1], E2);
      `checkd(en3[2], E0);
    end

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
