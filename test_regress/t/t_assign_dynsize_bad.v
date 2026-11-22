// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Non-blocking, continuous and procedural continuous assignments shall not write elements of
// dynamically sized variables, or parts of them, but may write the variables whole. Procedural
// continuous assignments shall not read them either (IEEE 1800-2023 6.21)

class Cls;
  static int s_dyn[];
endclass

typedef struct {
  int aa[int];
  int da[];
  int q[$];
} dyn_t;

module t (
    input clk
);
  int i;

  // Non-blocking assignments
  int nq[$];
  int nq2[$];
  always @(posedge clk) begin
    nq <= nq2;  // OK
    nq[i] <= 1;  // Error
    nq[i][7:0] <= 1;  // Error
    nq[0] <= 1;  // Error
    nq[0][7:0] <= 1;  // Error
  end

  int nd[];
  int nd2[];
  always @(posedge clk) begin
    nd <= nd2;  // OK
    nd[i] <= 1;  // Error
    nd[i][7:0] <= 1;  // Error
    nd[0] <= 1;  // Error
    nd[0][7:0] <= 1;  // Error
  end

  int na[int];
  int na2[int];
  always @(posedge clk) begin
    na <= na2;  // OK
    na[i] <= 1;  // Error
    na[i][7:0] <= 1;  // Error
    na[0] <= 1;  // Error
    na[0][7:0] <= 1;  // Error
  end

  int nw[*];
  always @(posedge clk) begin
    nw <= '{default: 0};  // OK
    nw[i] <= 1;  // Error
    nw[i][7:0] <= 1;  // Error
    nw[0] <= 1;  // Error
    nw[0][7:0] <= 1;  // Error
  end

  string ns;
  string nsa[2];
  always @(posedge clk) begin
    ns <= "ab";  // OK
    nsa[i] <= "ab";  // OK
    nsa[0] <= "ab";  // OK
    ns[i] <= "x";  // Error
    nsa[i][i] <= "x";  // Error
    ns[0] <= "x";  // Error
    nsa[0][0] <= "x";  // Error
  end

  // Static class members, also via a handle, struct members, and in arrays
  Cls nc[1];
  int nci[];
  dyn_t nst;
  dyn_t nsta[2];
  int naa[2][int];
  int nad[2][];
  always @(posedge clk) begin
    Cls::s_dyn <= nd2;  // OK
    Cls::s_dyn[0] <= 1;  // Error
    nc[nci[0]++].s_dyn <= nd2;  // OK
    nc[nci[0]++].s_dyn[0] <= 1;  // Error
    nst.da <= nd2;  // OK
    nst.aa[0] <= 1;  // Error
    nst.da[0] <= 1;  // Error
    nst.q[0] <= 1;  // Error
    nsta[1].da[0] <= 1;  // Error
    naa[0][0] <= 1;  // Error
    nad[0][0] <= 1;  // Error
  end

  // Reading them is allowed
  int nok[2];
  always @(posedge clk) begin
    nok[nst.da[0]!=0] <= nst.da[1];  // OK
    nok[naa[0][0]!=0] <= 1;  // OK
  end

  // Continuous assignments
  int cq[$];
  int cq2[$];
  assign cq2 = cq;  // OK
  assign cq[0] = 1;  // Error
  assign cq[1][7:0] = 1;  // Error

  int cd[];
  int cd2[];
  assign cd2 = cd;  // OK
  assign cd[0] = 1;  // Error
  assign cd[1][7:0] = 1;  // Error

  int ca[int];
  int ca2[int];
  assign ca2 = ca;  // OK
  assign ca[0] = 1;  // Error
  assign ca[1][7:0] = 1;  // Error

  int cw[*];
  int cw2[*];
  assign cw2 = '{default: 0};  // OK
  assign cw[0] = 1;  // Error
  assign cw[1][7:0] = 1;  // Error

  string cs;
  string cs2;
  string csa[2];
  assign cs2 = cs;  // OK
  assign csa[1] = cs;  // OK
  assign cs[0] = "x";  // Error
  assign csa[0][0] = "x";  // Error

  dyn_t cst;
  assign cst.da[0] = 1;  // Error

  // Procedural continuous assignments, which shall not read them either
  int pq[$];
  int pq2[$];
  int pr;
  byte pr8;
  bit [7:0] pb;
  bit pbit;
  string ps;
  string ps2;
  string psa[2];
  dyn_t pst;
  int pw[*];
  int paa[2][int];
  initial begin
    // verilator lint_off IEEEMAYDEPRECATE
    assign pq2 = pq;  // OK
    assign pq[0] = 1;  // Error
    assign pr = pq[0];  // Error
    assign pr8 = pq[0][7:0];  // Error
    assign pbit = pb[pq[0]];  // Error
    assign ps2 = ps;  // OK
    assign ps[0] = "x";  // Error
    assign psa[0][0] = "x";  // Error
    assign pr8 = ps[0];  // Error
    assign pr8 = psa[0][0];  // Error
    assign pr = pst.da[0];  // Error
    assign pr = pw[0];  // Error
    assign pr = paa[0][0];  // Error
    // verilator lint_on IEEEMAYDEPRECATE
  end
  // Force and release statements, also procedural continuous assignments (IEEE 1800-2023
  // 10.6.2), and so also not of non-static class properties nor automatic variables
  typedef logic [6:0] frow_t[3:2];
  typedef struct {
    logic [6:0] q[$];
    logic [6:0] d[];
    logic [6:0] a[int];
    logic [6:0] w[*];
    frow_t ar[int];
    frow_t qr[$];
    frow_t f;
  } fdyn_t;
  class FCls;
    logic [6:0] p;
    frow_t pa;
  endclass

  logic [6:0] fq[$];
  logic [6:0] fd[];
  logic [6:0] fa[int];
  logic [6:0] fw[*];
  frow_t fqr[$];
  frow_t ff;
  initial begin
    force ff[2] = 7'h55;  // OK
    force fq[1] = 7'h55;  // Error
    force fd[1] = 7'h55;  // Error
    force fa[3] = 7'h55;  // Error
    force fw[3] = 7'h55;  // Error
    force fq[1][5:3] = 3'h5;  // Error
    force fq[$] = 7'h55;  // Error
    force fq[$-1] = 7'h55;  // Error
    force fqr[$][2] = 7'h55;  // Error
    release ff[2];  // OK
    release fq[1];  // Error
    release fq[$];  // Error
  end

  // Also of struct members
  fdyn_t fs;
  initial begin
    force fs.f[2] = 7'h55;  // OK
    force fs.q[1] = 7'h55;  // Error
    force fs.d[1] = 7'h55;  // Error
    force fs.a[3] = 7'h55;  // Error
    force fs.w[3] = 7'h55;  // Error
    force fs.ar[3][2] = 7'h55;  // Error
    force fs.qr[$][2] = 7'h55;  // Error
    release fs.a[3];  // Error
  end

  // Also of interface members
  FIfc fifc ();
  initial force fifc.w[3][2] = 7'h55;  // Error

  // Non-static class properties, also in a conditional statement
  FCls fc;
  frow_t ff2;
  bit fen;
  initial begin
    force fc.p = 7'h55;  // Error
    force fc.pa[2] = 7'h55;  // Error
    if (fen) force fc.pa = ff2;  // Error
    release fc.p;  // Error
  end

  // Automatic variables
  initial begin
    automatic logic [6:0] fav;
    force fav = 7'h55;  // Error
  end
endmodule

interface FIfc;
  logic [6:0] w[*][3:2];
endinterface
