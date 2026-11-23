// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
  } us_t;
  typedef logic [7:0] pair_t[2];
  typedef pair_t pairq_t[$];
  typedef string sqt_t[$];

  initial begin
    logic [7:0] uq[$][2];
    us_t usd[];
    pairq_t pq;
    string sq[$];
    string sd[];
    sqt_t sqt;
    string sa[2];
    string s;
    s = {>>{uq}};
    s = {>>{usd}};
    s = {<<8{pq}};
    s = {<<8{sq}};
    s = {<<{sd}};
    s = {<<16{sqt}};
    s = {>>{sa}};
  end
endmodule
