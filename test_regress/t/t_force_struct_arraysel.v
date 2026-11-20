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
  st_t s;
  st_t s2;  // Only s2.flag is forced
  st_t so;  // Only so.mem is forced
  st_t sr;  // sr.mem is only released
  top_t n;
  dyn_t d;
  logic [7:0] q;
  logic [7:0] m;
  int i;
  assign q = s.arr[1].value;
  assign m = s.mem[1];

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
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
