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
  // Example of the issue, a force beside an array of structs that is read
  typedef struct {
    struct {logic [7:0] value;} arr[2];
    logic flag;
  } issue_t;
  issue_t si;
  logic [7:0] qi;
  assign qi = si.arr[1].value;
  initial begin
    si.arr[1].value = 8'h5a;
    force si.flag = 1'b1;
    #1;
    `checkh(qi, 8'h5a);
    `checkh(si.flag, 1'b1);
  end

  typedef struct {
    struct {logic [6:0] value;} arr[3:2];
    logic [64:0] mem[1:2];
    logic flag;
  } st_t;

  // Force outside and then inside of the arrays, read by continuous assignments
  st_t s;
  logic [6:0] q;
  logic [64:0] m;
  assign q = s.arr[3].value;
  assign m = s.mem[2];
  initial begin
    s.arr[2].value = 7'h01;
    s.arr[3].value = 7'h5a;
    s.mem[1] = 65'h1_0000_0000_0000_0002;
    s.mem[2] = 65'h1_0000_0000_0000_0003;
    s.flag = 1'b0;
    force s.flag = 1'b1;
    #1;
    `checkh(q, 7'h5a);
    `checkh(m, 65'h1_0000_0000_0000_0003);
    `checkh(s.flag, 1'b1);
    force s.arr[3].value = 7'h25;
    force s.mem[2] = 65'h1_0000_0000_0000_0030;
    s.arr[3].value = 7'h66;
    #1;
    `checkh(q, 7'h25);
    `checkh(m, 65'h1_0000_0000_0000_0030);
    `checkh(s.arr[2].value, 7'h01);
    `checkh(s.mem[1], 65'h1_0000_0000_0000_0002);
    `checkh(s.flag, 1'b1);
    release s.arr[3].value;
    release s.mem[2];
    #1;
    `checkh(q, 7'h25);
    `checkh(m, 65'h1_0000_0000_0000_0030);
    s.arr[3].value = 7'h67;
    s.mem[2] = 65'h0_8000_0000_0000_0004;
    #1;
    `checkh(q, 7'h67);
    `checkh(m, 65'h0_8000_0000_0000_0004);
    `checkh(s.flag, 1'b1);
  end

  // Non-constant index read, force outside of the arrays
  st_t s2;
  initial begin
    int i;
    s2.arr[2].value = 7'h3c;
    s2.arr[3].value = 7'h3d;
    s2.flag = 1'b0;
    force s2.flag = 1'b1;
    for (i = 2; i <= 3; ++i) begin
      #1;
      `checkh(s2.arr[i].value, 7'h3a + 7'(i));
    end
    `checkh(s2.flag, 1'b1);
  end

  // Non-constant index read of an array beside the one with a forced element
  st_t so;
  initial begin
    int i;
    so.arr[2].value = 7'h4c;
    so.arr[3].value = 7'h4d;
    so.mem[1] = 65'h1_0000_0000_0000_0005;
    force so.mem[2] = 65'h1_0000_0000_0000_0031;
    for (i = 2; i <= 3; ++i) begin
      #1;
      `checkh(so.arr[i].value, 7'h4a + 7'(i));
    end
    `checkh(so.mem[1], 65'h1_0000_0000_0000_0005);
    `checkh(so.mem[1][64:60], 5'h10);
    `checkh(so.mem[2], 65'h1_0000_0000_0000_0031);
    force so.mem[2] = 65'h1_0000_0000_0000_0032;
    #1;
    `checkh(so.mem[2], 65'h1_0000_0000_0000_0032);
  end

  // Non-constant index read of an array with an element only released
  st_t sr;
  initial begin
    int i;
    sr.mem[1] = 65'h1_0000_0000_0000_0006;
    sr.mem[2] = 65'h1_0000_0000_0000_0007;
    sr.flag = 1'b0;
    force sr.flag = 1'b1;
    release sr.mem[2];
    for (i = 1; i <= 2; ++i) begin
      #1;
      `checkh(sr.mem[i], 65'h1_0000_0000_0000_0005 + 65'(i));
    end
    `checkh(sr.flag, 1'b1);
  end

  // Member of a struct in an array in a struct member
  typedef struct {
    logic [2:0] f;
    logic [4:0] g;
  } leaf_t;
  typedef struct {
    leaf_t l[2:1];
    logic [6:0] tag;
  } mid_t;
  typedef struct {
    mid_t m;
    int id;
  } top_t;
  top_t n;
  initial begin
    n.m.l[1].f = 3'h1;
    n.m.l[1].g = 5'h02;
    n.m.l[2].f = 3'h3;
    n.m.l[2].g = 5'h04;
    n.m.tag = 7'h55;
    n.id = 9;
    force n.m.l[2].g = 5'h1a;
    #1;
    `checkh(n.m.l[2].g, 5'h1a);
    `checkh(n.m.l[2].f, 3'h3);
    `checkh(n.m.l[1].g, 5'h02);
    `checkh(n.m.tag, 7'h55);
    n.m.l[2].g = 5'h00;
    n.m.l[2].f = 3'h6;
    #1;
    `checkh(n.m.l[2].g, 5'h1a);
    `checkh(n.m.l[2].f, 3'h6);
    release n.m.l[2].g;
    n.m.l[2].g = 5'h01;
    #1;
    `checkh(n.m.l[2].g, 5'h01);
    `checkh(n.id, 9);
  end

  typedef struct {logic [6:0] x[3:2];} ua_t;
  typedef struct {logic [6:0] y[3:2];} ub_t;
  typedef union {
    ua_t a;
    ub_t b;
  } u_t;

  // Non-constant index read through a union beside the array with a forced element
  typedef struct {
    u_t u;
    ua_t e[2:1];
  } su_t;
  su_t su;
  initial begin
    int i;
    su.u.b.y[2] = 7'h43;
    su.u.b.y[3] = 7'h44;
    su.e[1].x[2] = 7'h05;
    force su.e[1].x[2] = 7'h55;
    for (i = 2; i <= 3; ++i) begin
      #1;
      `checkh(su.u.b.y[i], 7'h41 + 7'(i));
    end
    `checkh(su.e[1].x[2], 7'h55);
  end

  typedef struct {
    logic [6:0] v;
    logic [6:0] arr[3:2];
  } elem_t;
  typedef struct {
    logic [6:0] q[$][3:2];
    logic [6:0] aa[int][1:2];
    logic [6:0] wa[*];
    logic [6:0] dyn[];
    elem_t qe[$];
    elem_t ae[string];
    u_t au[int];
    logic [6:0] fixed[3:2];
    logic flag;
  } dyn_t;

  // Reads through queues, associative and dynamic arrays, which cannot be forced
  dyn_t d;
  initial begin
    int i;
    d.q.push_back('{7'h13, 7'h12});
    d.aa[5][1] = 7'h32;
    d.aa[5][2] = 7'h33;
    d.wa[7] = 7'h44;
    d.dyn = new[5];
    d.dyn[3] = 7'h52;
    d.dyn[4] = 7'h53;
    d.qe.push_back('{7'h66, '{7'h73, 7'h72}});
    d.ae["k"].v = 7'h19;
    d.ae["k"].arr[2] = 7'h62;
    d.ae["k"].arr[3] = 7'h63;
    d.flag = 1'b0;
    force d.flag = 1'b1;
    for (i = 2; i <= 3; ++i) begin
      #1;
      `checkh(d.q[0][i], 7'h10 + 7'(i));
      `checkh(d.aa[5][i-1], 7'h30 + 7'(i));
      `checkh(d.dyn[i+1], 7'h50 + 7'(i));
      `checkh(d.qe[0].arr[i], 7'h70 + 7'(i));
      `checkh(d.ae["k"].arr[i], 7'h60 + 7'(i));
    end
    `checkh(d.q[0][2], 7'h12);
    `checkh(d.q.size(), 1);
    `checkh(d.aa[5][1], 7'h32);
    `checkh(d.wa[7], 7'h44);
    `checkh(d.dyn[3], 7'h52);
    `checkh(d.qe[0].v, 7'h66);
    `checkh(d.ae["k"].v, 7'h19);
    `checkh(d.flag, 1'b1);
  end

  // Such reads beside a forced element of an array of the struct
  dyn_t df;
  initial begin
    int i;
    df.qe.push_back('{7'h66, '{7'h73, 7'h72}});
    df.ae["k"].arr[2] = 7'h62;
    df.ae["k"].arr[3] = 7'h63;
    df.au[4].b.y[2] = 7'h42;
    df.au[4].b.y[3] = 7'h43;
    df.fixed[2] = 7'h01;
    df.fixed[3] = 7'h02;
    force df.fixed[3] = 7'h55;
    for (i = 2; i <= 3; ++i) begin
      #1;
      `checkh(df.qe[0].arr[i], 7'h70 + 7'(i));
      `checkh(df.ae["k"].arr[i], 7'h60 + 7'(i));
      `checkh(df.au[4].b.y[i], 7'h40 + 7'(i));
    end
    `checkh(df.fixed[2], 7'h01);
    `checkh(df.fixed[3], 7'h55);
  end

  // Elements of associative array members that are forced
  typedef struct {
    logic [6:0] aa[int];
    elem_t ae[string];
    logic flag;
  } assoc_t;
  assoc_t sa;
  logic [6:0] vaa[int];
  elem_t vae[string];
  initial begin
    int i;
    sa.aa[2] = 7'h12;
    sa.aa[3] = 7'h13;
    sa.ae["k"].arr[2] = 7'h22;
    sa.ae["k"].arr[3] = 7'h23;
    vaa[2] = 7'h42;
    vaa[3] = 7'h43;
    vae["k"].arr[2] = 7'h52;
    vae["k"].arr[3] = 7'h53;
    force sa.aa = vaa;
    force sa.ae = vae;
    for (i = 2; i <= 3; ++i) begin
      #1;
      `checkh(sa.aa[i], 7'h40 + 7'(i));
      `checkh(sa.ae["k"].arr[i], 7'h50 + 7'(i));
    end
    `checkh(sa.aa[3], 7'h43);
    `checkh(sa.ae["k"].arr[3], 7'h53);
    sa.aa[3] = 7'h15;
    sa.ae["k"].arr[3] = 7'h25;
    #1;
    `checkh(sa.aa[3], 7'h43);
    `checkh(sa.ae["k"].arr[3], 7'h53);
    release sa.aa;
    release sa.ae;
    #1;
    `checkh(sa.aa[3], 7'h43);
    `checkh(sa.ae["k"].arr[3], 7'h53);
    sa.aa[3] = 7'h16;
    sa.ae["k"].arr[3] = 7'h26;
    #1;
    `checkh(sa.aa[3], 7'h16);
    `checkh(sa.ae["k"].arr[3], 7'h26);
  end

  typedef struct {
    logic [6:0] m[3:1];
    logic [4:0] m2[1:2][5:3];
    logic [2:0] k;
  } rel_t;

  // Whole array member forced and released
  rel_t r;
  logic [6:0] rm;
  assign rm = r.m[2];
  initial begin
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
  end

  // Elements forced, their row and the whole array member released
  rel_t rr;
  initial begin
    rr.m2[1][4] = 5'h04;
    rr.m2[2][3] = 5'h05;
    rr.m2[2][5] = 5'h06;
    force rr.m2[1][4] = 5'h14;
    force rr.m2[2][3] = 5'h15;
    #1;
    release rr.m2[2];
    #1;
    `checkh(rr.m2[2][3], 5'h15);
    rr.m2[2][3] = 5'h07;
    rr.m2[1][4] = 5'h08;
    #1;
    `checkh(rr.m2[2][3], 5'h07);
    `checkh(rr.m2[1][4], 5'h14);
    release rr.m2;
    #1;
    `checkh(rr.m2[1][4], 5'h14);
    rr.m2[1][4] = 5'h09;
    #1;
    `checkh(rr.m2[1][4], 5'h09);
    `checkh(rr.m2[2][5], 5'h06);
  end

  // Part-select of a member forced, the member and the whole variable released
  rel_t rp;
  initial begin
    rp.m[3] = 7'h53;
    rp.k = 3'h1;
    force rp.k[2:1] = 2'h2;
    #1;
    `checkh(rp.k[2:1], 2'h2);
    release rp.k;
    #1;
    `checkh(rp.k, 3'h5);
    rp.k = 3'h2;
    #1;
    `checkh(rp.k, 3'h2);
    force rp.k[2:1] = 2'h2;
    #1;
    release rp;
    #1;
    `checkh(rp.k, 3'h4);
    `checkh(rp.m[3], 7'h53);
    rp.k = 3'h1;
    #1;
    `checkh(rp.k, 3'h1);
  end

  // Members of an array element forced, the element and then the whole variable released
  typedef struct {
    rel_t e[2:3];
    logic flag;
  } rel_outer_t;
  rel_outer_t ro;
  initial begin
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
  end

  // Whole variable forced, then a member of an array element, the whole variable released
  rel_outer_t rw;
  rel_outer_t rwv;
  initial begin
    rwv.e[2].k = 3'h1;
    rwv.e[3].m[2] = 7'h42;
    rwv.e[3].k = 3'h2;
    rwv.flag = 1'b1;
    rw.e[2].k = 3'h7;
    rw.e[3].m[2] = 7'h72;
    rw.e[3].k = 3'h6;
    rw.flag = 1'b0;
    force rw = rwv;
    force rw.e[3].k = 3'h5;
    #1;
    `checkh(rw.e[3].k, 3'h5);
    release rw;
    #1;
    `checkh(rw.e[3].k, 3'h5);
    `checkh(rw.e[2].k, 3'h1);
    `checkh(rw.e[3].m[2], 7'h42);
    `checkh(rw.flag, 1'b1);
    rw.e[3].k = 3'h3;
    rw.e[2].k = 3'h4;
    #1;
    `checkh(rw.e[3].k, 3'h3);
    `checkh(rw.e[2].k, 3'h4);
    `checkh(rw.flag, 1'b1);
  end

  // Continuously driven element returns to the driven value
  rel_t rc;
  logic [6:0] drv;
  assign rc.m[1] = drv;
  initial begin
    drv = 7'h31;
    force rc.m[1] = 7'h71;
    #1;
    `checkh(rc.m[1], 7'h71);
    release rc.m;
    #1;
    `checkh(rc.m[1], 7'h31);
  end

  // After every case
  initial begin
    #20;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
