// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets whose type or leaf type carries no bit vector, and an aggregate with too many leaves
class cls_t;
  int v;
endclass

typedef struct {
  logic [7:0] b;
  int w[*];
} ws_t;

typedef struct {
  string      t;
  real        r;
  logic [7:0] b;
} mixed_t;

module top_module;
  cls_t ch;
  int q[$];
  int wa[*];
  ws_t mws;
  int warr[2][*];
  mixed_t m;
  mixed_t mw;
  real rs[2];
  logic [7:0] bigmem[512];

  initial begin
    q.push_back(1);
    wa[3] = 2;
    mws.b = 8'h01;
    mws.w[1] = 3;
    warr[1][2] = 4;
    m.t = "ab";
    m.r = 1.5;
    mw.b = 8'h02;
    rs[0] = 2.5;
    bigmem[0] = 8'h03;
    #1 $display("%0d %0d %x %0d %0d %0d", q[0], wa[3], mws.b, mws.w[1], warr[1][2], ch == null);
    $display("%s %f %x %f %x", m.t, m.r, mw.b, rs[0], bigmem[0]);
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
