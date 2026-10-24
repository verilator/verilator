// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface a_if;
  int x;
endinterface

typedef virtual a_if va_t;

module sub;
  a_if ifs[2] ();
  for (genvar i = 0; i < 2; ++i) begin : g
    initial ifs[i].x = 'h40 + i;
  end
endmodule

class C;
  va_t vif[2];
endclass

module t;

  a_if asc[0:3] ();
  a_if desc[3:0] ();
  a_if a2d[1:0][0:2] ();

  for (genvar i = 0; i < 4; ++i) begin : g_1d
    initial begin
      asc[i].x = 'h10 + i;
      desc[i].x = 'h20 + i;
    end
  end
  for (genvar i = 0; i < 2; ++i) begin : g_2d_i
    for (genvar j = 0; j < 3; ++j) begin : g_2d_j
      initial a2d[i][j].x = 'h30 + 3 * i + j;
    end
  end

  va_t w[4];
  va_t s[2];
  va_t w2d[2][3];
  C c;

  sub i_sub ();

  initial begin
    #1;
    // Whole array, left element to left element
    w = asc;
    for (int i = 0; i < 4; ++i) `checkh(w[i].x, 'h10 + i);
    w = desc;
    for (int i = 0; i < 4; ++i) `checkh(w[i].x, 'h20 + 3 - i);
    // Slices
    s = asc[1:2];
    `checkh(s[0].x, 'h11);
    `checkh(s[1].x, 'h12);
    s = desc[2:1];
    `checkh(s[0].x, 'h22);
    `checkh(s[1].x, 'h21);
    // Multi dimensional, a2d[1] is the left row
    w2d = a2d;
    for (int i = 0; i < 2; ++i) begin
      for (int j = 0; j < 3; ++j) `checkh(w2d[i][j].x, 'h30 + 3 * (1 - i) + j);
    end
    // Hierarchical reference to a whole array
    s = i_sub.ifs;
    `checkh(s[0].x, 'h40);
    `checkh(s[1].x, 'h41);
    `checkh(i_sub.ifs[0].x, 'h40);
    `checkh(i_sub.ifs[1].x, 'h41);
    // Class member
    c = new;
    c.vif = asc[2:3];
    `checkh(c.vif[0].x, 'h12);
    `checkh(c.vif[1].x, 'h13);
    // Writes through the virtual interfaces reach the instances
    c.vif[1].x = 'h99;
    w2d[0][2].x = 'h98;
    #1;
    `checkh(asc[3].x, 'h99);
    `checkh(a2d[1][2].x, 'h98);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
