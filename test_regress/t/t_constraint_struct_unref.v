// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Regression for: a random member of a rand unpacked struct that no constraint
// references must still be randomized (IEEE 1800-2023 18.4 - all random
// members of a rand unpacked struct are solved concurrently).

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin \
   $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkgt(gotv,minv) do if (!((gotv) > (minv))) begin \
   $write("%%Error: %s:%0d:  got=%0d expected > %0d\n", `__FILE__, `__LINE__, (gotv), (minv)); `stop; end while(0)
// verilog_format: on

typedef struct {
  rand bit [3:0] inner_id;  // UNCONSTRAINED nested random member
} inner_t;

typedef struct {
  rand bit [3:0] id;  // UNCONSTRAINED random member
  rand bit [2:0] size;  // constrained random member
  rand inner_t inner;  // UNCONSTRAINED nested rand struct member
  bit [3:0] fixed;  // non-rand member: must keep its value
} unpacked_t;

typedef struct packed {
  bit [3:0] id;
  bit [2:0] size;
} packed_t;

class C;
  rand unpacked_t u;
  rand packed_t p;
  // Reference ONLY .size on each; .id, .inner.inner_id are random members left
  // unmentioned, and .fixed is a non-rand member.
  constraint c {
    u.size inside {[0 : 2]};
    p.size inside {[0 : 2]};
  }
  function new();
    u.fixed = 4'hA;
  endfunction
endclass

// Shared struct type as a non-rand member of a different randomized class.
class D;
  unpacked_t m;
  rand bit [3:0] z;
  constraint dz {z < 5;}
endclass

// Struct-in-struct: constraint reaches into the nested struct.
typedef struct {
  rand bit [3:0] a;  // constrained nested member
  rand bit [3:0] b;  // UNCONSTRAINED nested member
} inner2_t;

typedef struct {
  rand inner2_t inr;
  rand bit [3:0] x;  // UNCONSTRAINED outer member
} outer_t;

class E;
  rand outer_t o;
  constraint eo {o.inr.a < 3;}
endclass

// A rand member with an initializer, and a randc member, both unreferenced.
typedef struct {
  rand bit [3:0] wi = 4'h1;  // rand member with initializer
  randc bit [3:0] cyc;  // randc member
  rand bit [3:0] r;  // constrained member
} extra_t;

class F;
  rand extra_t s;
  constraint fc {s.r < 5;}
endclass

// Unpacked array of struct as a rand member, left unreferenced by the constraint.
typedef struct {rand bit [3:0] f;} aelem_t;

typedef struct {
  rand bit [3:0] g;
  rand aelem_t es[2];
} arr_t;

class G;
  rand arr_t o;
  constraint gc {o.g < 5;}
endclass

module t_constraint_struct_unref;
  initial begin
    C c;
    D d;
    E e;
    F f;
    G g;
    int uid[16];
    int pid[16];
    int iid[16];
    int zid[16];
    int bid[16];
    int xid[16];
    int wid[16];
    int cid[16];
    int e0id[16];
    int e1id[16];
    int un;
    int pn;
    int inn;
    int zn;
    int bn;
    int xn;
    int wn;
    int cn;
    int e0n;
    int e1n;
    // Non-randomized use of the shared type: must stay untouched.
    unpacked_t plain;
    outer_t plain2;
    c = new();
    d = new();
    e = new();
    f = new();
    g = new();
    un = 0;
    pn = 0;
    inn = 0;
    zn = 0;
    bn = 0;
    xn = 0;
    wn = 0;
    cn = 0;
    e0n = 0;
    e1n = 0;
    plain.id = 4'h5;
    plain.size = 3'h6;
    plain.inner.inner_id = 4'h7;
    plain.fixed = 4'h8;
    d.m.id = 4'h1;
    d.m.size = 3'h2;
    d.m.inner.inner_id = 4'h3;
    d.m.fixed = 4'h4;
    plain2.inr.a = 4'h9;
    plain2.inr.b = 4'hA;
    plain2.x = 4'hB;
    for (int i = 0; i < 300; i++) begin
      `checkd(c.randomize(), 1);
      `checkd((c.u.size inside {[0 : 2]}), 1'b1);
      `checkd((c.p.size inside {[0 : 2]}), 1'b1);
      `checkd(c.u.fixed, 4'hA);
      uid[c.u.id]++;
      pid[c.p.id]++;
      iid[c.u.inner.inner_id]++;
      `checkd(d.randomize(), 1);
      `checkd((d.z < 5), 1'b1);
      `checkd(d.m.id, 4'h1);
      `checkd(d.m.size, 3'h2);
      `checkd(d.m.inner.inner_id, 4'h3);
      `checkd(d.m.fixed, 4'h4);
      zid[d.z]++;
      `checkd(e.randomize(), 1);
      `checkd((e.o.inr.a < 3), 1'b1);
      bid[e.o.inr.b]++;  // unreferenced nested member
      xid[e.o.x]++;  // unreferenced outer member
      `checkd(f.randomize(), 1);
      `checkd((f.s.r < 5), 1'b1);
      wid[f.s.wi]++;  // unreferenced rand member with initializer
      cid[f.s.cyc]++;  // unreferenced randc member
      `checkd(g.randomize(), 1);
      `checkd((g.o.g < 5), 1'b1);
      e0id[g.o.es[0].f]++;  // unreferenced array-of-struct element
      e1id[g.o.es[1].f]++;
    end
    foreach (uid[k]) if (uid[k] > 0) un++;
    foreach (pid[k]) if (pid[k] > 0) pn++;
    foreach (iid[k]) if (iid[k] > 0) inn++;
    foreach (zid[k]) if (zid[k] > 0) zn++;
    foreach (bid[k]) if (bid[k] > 0) bn++;
    foreach (xid[k]) if (xid[k] > 0) xn++;
    foreach (wid[k]) if (wid[k] > 0) wn++;
    foreach (cid[k]) if (cid[k] > 0) cn++;
    foreach (e0id[k]) if (e0id[k] > 0) e0n++;
    foreach (e1id[k]) if (e1id[k] > 0) e1n++;
    // Unreferenced rand members must vary; packed struct is the control case.
    `checkgt(un, 7);
    `checkgt(pn, 7);
    `checkgt(inn, 7);
    `checkgt(zn, 3);
    `checkgt(bn, 7);
    `checkgt(xn, 7);
    `checkgt(wn, 7);
    `checkgt(cn, 7);
    `checkgt(e0n, 7);
    `checkgt(e1n, 7);
    `checkd(plain.id, 4'h5);
    `checkd(plain.size, 3'h6);
    `checkd(plain.inner.inner_id, 4'h7);
    `checkd(plain.fixed, 4'h8);
    `checkd(plain2.inr.a, 4'h9);
    `checkd(plain2.inr.b, 4'hA);
    `checkd(plain2.x, 4'hB);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
