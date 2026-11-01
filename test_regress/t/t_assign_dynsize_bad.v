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
    nok[nst.da[0] != 0] <= nst.da[1];  // OK
    nok[naa[0][0] != 0] <= 1;  // OK
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
endmodule
