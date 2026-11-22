// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  typedef struct {
    struct {logic [7:0] value;} arr[2];
    logic [7:0] mem[2];
    logic flag;
  } st_t;
  typedef struct {
    logic [3:0] f;
    logic [3:0] g;
  } leaf_t;
  typedef struct {
    leaf_t l[2];
    logic [7:0] tag;
  } mid_t;
  typedef struct {
    mid_t m;
    int id;
  } top_t;
  typedef struct {
    logic [7:0] v;
    logic [7:0] arr[2];
  } elem_t;
  typedef struct {
    logic [7:0] q[$][2];
    logic [7:0] aa[int][2];
    logic [7:0] wa[*];
    logic [7:0] dyn[];
    elem_t qe[$];
    elem_t ae[string];
    logic flag;
  } dyn_t;
  typedef struct {
    logic [6:0] m[3:1];
    logic [4:0] m2[1:2][5:3];
    logic [2:0] k;
  } rel_t;
  typedef struct {
    rel_t e[2:3];
    logic flag;
  } rel_outer_t;
  typedef struct {logic [6:0] x[3:2];} ua_t;
  typedef struct {logic [6:0] y[3:2];} ub_t;
  typedef union {
    ua_t a;
    ub_t b;
  } u_t;
  typedef struct {
    u_t u;
    ua_t e[2:1];
  } su_t;
  st_t s;
  st_t s2;  // Only s2.flag is forced
  st_t so;  // Only so.mem is forced
  st_t sr;  // sr.mem is only released
  su_t su;  // Only su.e is forced, outside of the union
  top_t n;
  dyn_t d;
  rel_t r;  // Released above the forced paths
  rel_outer_t ro;
  rel_t rc;  // rc.m[1] is continuously driven
  logic [7:0] q;
  logic [7:0] m;
  logic [6:0] rm;
  logic [6:0] drv;
  int i;
  assign q = s.arr[1].value;
  assign m = s.mem[1];
  assign rm = r.m[2];
  assign rc.m[1] = drv;

  initial begin
    s.arr[0].value = 8'h01;
    s.arr[1].value = 8'h5a;
    s.mem[0] = 8'h02;
    s.mem[1] = 8'h03;
    s.flag = 1'b0;
    // Force outside of the arrays
    force s.flag = 1'b1;
    #1;
    `checkh(q, 8'h5a);
    `checkh(m, 8'h03);
    `checkh(s.flag, 1'b1);
    // Non-constant index read, force outside of the arrays
    s2.arr[1].value = 8'h3c;
    s2.flag = 1'b0;
    force s2.flag = 1'b1;
    i = 1;
    #1;
    `checkh(s2.arr[i].value, 8'h3c);
    `checkh(s2.flag, 1'b1);
    // Force inside of the arrays
    force s.arr[1].value = 8'ha5;
    force s.mem[1] = 8'h30;
    s.arr[1].value = 8'h66;
    #1;
    `checkh(q, 8'ha5);
    `checkh(m, 8'h30);
    `checkh(s.arr[0].value, 8'h01);
    `checkh(s.mem[0], 8'h02);
    `checkh(s.flag, 1'b1);
    release s.arr[1].value;
    release s.mem[1];
    #1;
    `checkh(q, 8'ha5);
    `checkh(m, 8'h30);
    s.arr[1].value = 8'h67;
    s.mem[1] = 8'h04;
    #1;
    `checkh(q, 8'h67);
    `checkh(m, 8'h04);
    `checkh(s.flag, 1'b1);
    // Member of a struct in an array in a struct member
    n.m.l[0].f = 4'h1;
    n.m.l[0].g = 4'h2;
    n.m.l[1].f = 4'h3;
    n.m.l[1].g = 4'h4;
    n.m.tag = 8'h55;
    n.id = 9;
    force n.m.l[1].g = 4'ha;
    #1;
    `checkh(n.m.l[1].g, 4'ha);
    `checkh(n.m.l[1].f, 4'h3);
    `checkh(n.m.l[0].g, 4'h2);
    `checkh(n.m.tag, 8'h55);
    n.m.l[1].g = 4'h0;
    n.m.l[1].f = 4'h6;
    #1;
    `checkh(n.m.l[1].g, 4'ha);
    `checkh(n.m.l[1].f, 4'h6);
    release n.m.l[1].g;
    n.m.l[1].g = 4'h1;
    #1;
    `checkh(n.m.l[1].g, 4'h1);
    `checkh(n.id, 9);
    // Non-constant index read of an array beside the one with a forced element
    so.arr[1].value = 8'h4d;
    so.mem[0] = 8'h05;
    force so.mem[1] = 8'h31;
    #1;
    `checkh(so.arr[i].value, 8'h4d);
    `checkh(so.mem[0], 8'h05);
    `checkh(so.mem[1], 8'h31);
    // Non-constant index read of an array with an element only released
    sr.mem[1] = 8'h06;
    sr.flag = 1'b0;
    force sr.flag = 1'b1;
    release sr.mem[1];
    #1;
    `checkh(sr.mem[i], 8'h06);
    `checkh(sr.flag, 1'b1);
    // Non-constant index read through a union beside the array with a forced element
    su.u.b.y[2] = 7'h43;
    su.u.b.y[3] = 7'h44;
    su.e[1].x[2] = 7'h05;
    force su.e[1].x[2] = 7'h55;
    #1;
    `checkh(su.u.b.y[i+1], 7'h43);
    `checkh(su.u.b.y[i+2], 7'h44);
    `checkh(su.e[1].x[2], 7'h55);
    // Reads through queues, associative and dynamic arrays, which cannot be forced
    d.q.push_back('{8'h11, 8'h22});
    d.aa[5][1] = 8'h33;
    d.wa[7] = 8'h44;
    d.dyn = new[3];
    d.dyn[2] = 8'h55;
    d.qe.push_back('{8'h66, '{8'h77, 8'h88}});
    d.ae["k"].v = 8'h99;
    d.ae["k"].arr[1] = 8'haa;
    d.flag = 1'b0;
    force d.flag = 1'b1;
    #1;
    `checkh(d.q[0][1], 8'h22);
    `checkh(d.q[0][i], 8'h22);
    `checkh(d.q.size(), 1);
    `checkh(d.aa[5][1], 8'h33);
    `checkh(d.aa[5][i], 8'h33);
    `checkh(d.wa[7], 8'h44);
    `checkh(d.dyn[2], 8'h55);
    `checkh(d.dyn[i+1], 8'h55);
    `checkh(d.qe[0].v, 8'h66);
    `checkh(d.qe[0].arr[i], 8'h88);
    `checkh(d.ae["k"].v, 8'h99);
    `checkh(d.ae["k"].arr[i], 8'haa);
    `checkh(d.flag, 1'b1);
    // Whole array member forced and released
    r.m[1] = 7'h11;
    r.m[2] = 7'h12;
    r.m[3] = 7'h13;
    force r.m = '{7'h53, 7'h52, 7'h51};
    #1;
    `checkh(r.m[1], 7'h51);
    `checkh(rm, 7'h52);
    release r.m;
    #1;
    `checkh(r.m[1], 7'h51);
    `checkh(rm, 7'h52);
    `checkh(r.m[3], 7'h53);
    r.m[1] = 7'h16;
    r.m[2] = 7'h17;
    #1;
    `checkh(r.m[1], 7'h16);
    `checkh(rm, 7'h17);
    `checkh(r.m[3], 7'h53);
    // Elements forced, their row and the whole array member released
    r.m2[1][4] = 5'h04;
    r.m2[2][3] = 5'h05;
    r.m2[2][5] = 5'h06;
    force r.m2[1][4] = 5'h14;
    force r.m2[2][3] = 5'h15;
    #1;
    release r.m2[2];
    #1;
    `checkh(r.m2[2][3], 5'h15);
    r.m2[2][3] = 5'h07;
    r.m2[1][4] = 5'h08;
    #1;
    `checkh(r.m2[2][3], 5'h07);
    `checkh(r.m2[1][4], 5'h14);
    release r.m2;
    #1;
    `checkh(r.m2[1][4], 5'h14);
    r.m2[1][4] = 5'h09;
    #1;
    `checkh(r.m2[1][4], 5'h09);
    `checkh(r.m2[2][5], 5'h06);
    // Part-select of a member forced, the member and the whole variable released
    r.k = 3'h1;
    force r.k[2:1] = 2'h2;
    #1;
    `checkh(r.k[2:1], 2'h2);
    release r.k;
    #1;
    `checkh(r.k, 3'h5);
    r.k = 3'h2;
    #1;
    `checkh(r.k, 3'h2);
    force r.k[2:1] = 2'h2;
    #1;
    release r;
    #1;
    `checkh(r.k, 3'h4);
    `checkh(r.m[3], 7'h53);
    r.k = 3'h1;
    #1;
    `checkh(r.k, 3'h1);
    // Members of an array element forced, the element released
    ro.e[2].k = 3'h1;
    ro.e[3].m[2] = 7'h21;
    ro.e[3].k = 3'h2;
    ro.flag = 1'b0;
    force ro.e[3].m[2] = 7'h61;
    force ro.e[3].k = 3'h5;
    #1;
    release ro.e[3];
    #1;
    `checkh(ro.e[3].m[2], 7'h61);
    `checkh(ro.e[3].k, 3'h5);
    ro.e[3].m[2] = 7'h22;
    ro.e[3].k = 3'h3;
    #1;
    `checkh(ro.e[3].m[2], 7'h22);
    `checkh(ro.e[3].k, 3'h3);
    // Whole variable released
    force ro.e[2].k = 3'h6;
    force ro.flag = 1'b1;
    #1;
    release ro;
    #1;
    `checkh(ro.e[2].k, 3'h6);
    `checkh(ro.flag, 1'b1);
    `checkh(ro.e[3].m[2], 7'h22);
    ro.e[2].k = 3'h4;
    ro.flag = 1'b0;
    #1;
    `checkh(ro.e[2].k, 3'h4);
    `checkh(ro.flag, 1'b0);
    `checkh(ro.e[3].k, 3'h3);
    // Continuously driven element returns to the driven value
    drv = 7'h31;
    force rc.m[1] = 7'h71;
    #1;
    `checkh(rc.m[1], 7'h71);
    release rc.m;
    #1;
    `checkh(rc.m[1], 7'h31);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
