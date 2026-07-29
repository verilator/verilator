// DESCRIPTION: Verilator: Verilog Test module
//
// Asserts how 'force' and 'release' behave when the target is a whole aggregate
// or overlaps an earlier force, per IEEE 1800-2023 10.6.1 and 10.6.2.  Where the
// standard does not describe overlapping force targets, an aggregate is held to
// the same rule as a packed vector.
//
// Each section below states what it asserts:
//  1. reading the whole struct while an element of an array member is forced,
//  2. a bit or part select of an element of an array member,
//  3. a whole plain unpacked array, which is one uniform stride,
//  4. a force replacing an earlier force over the range they share, and a
//     leaf release that punches a hole in an aggregate force,
//  5. aggregate forces nested three structs deep, in both activation orders,
//     with the middle one released while the outer stays active, and release
//     retention confined to what the released force owned,
//  6. more forces on one variable than a compiled read chain carries, so leaf
//     reads and release retention route through the whole-value shadow, and
//     re-executed identical force statements, which share one force entry,
//  7. one-element unpacked arrays, one- and multi-dimensional, whose element
//     and bit-select forces still take the slot path,
//  8. releasing an aggregate keeping a hole an earlier sub-region release
//     punched in it, rather than resurrecting the enclosing force there,
//  9. recomposing a whole-aggregate force over a non-bitwise single-slot hole
//     (an inner force on a real member).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%g exp=%g\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct {
  logic [7:0] arr[4];
  logic [7:0] scalar;
} st_t;

module t;

  typedef struct {
    logic [7:0] arr[4];
    logic [7:0] tail;
  } tail_t;
  typedef struct {
    logic [7:0] x;
    logic [7:0] y;
  } lvl0_t;
  typedef struct {
    lvl0_t sub;
    logic [7:0] pad;
  } lvl1_t;
  typedef struct {
    lvl1_t sub;
    logic [7:0] pad;
  } lvl2_t;
  typedef struct {
    logic [15:0] y;
    logic [7:0] z;
  } yz_t;
  typedef struct {
    real r;
    logic [7:0] a;
  } rb_t;

  st_t s;
  st_t src;
  st_t same;
  st_t snap;
  st_t q[2];
  st_t m[10];
  logic [7:0] tout;
  logic [7:0] parr[4];
  logic [7:0] pfill[4];
  logic [7:0] psnap[4];
  logic [7:0] vec;
  lvl2_t n;
  lvl2_t nsnap;
  lvl2_t z2;
  lvl1_t z1;
  lvl0_t z0;
  tail_t rt;
  tail_t rtsrc;
  logic [15:0] one[5:5];
  logic [7:0] onemd[2:2][7:7];
  yz_t hs, hrhs;
  rb_t rbs, rbsrc, rbsnap;

  // Copies the struct before selecting from it, so the whole value is materialised
  function automatic logic [7:0] via_copy(st_t v);
    st_t copy;
    copy = v;
    return copy.arr[2];
  endfunction

  task automatic grab(input st_t v, output logic [7:0] oval);
    oval = v.arr[2];
  endtask

  initial begin
    //=======================================================================
    // 1. Reading the whole struct while an element of an array member is
    //    forced, in the contexts where the struct value has to be materialised
    //=======================================================================
    for (int i = 0; i < 4; ++i) begin
      s.arr[i] = 8'h10 + 8'(i);
      same.arr[i] = 8'h10 + 8'(i);
      src.arr[i] = 8'h20 + 8'(i);
    end
    s.scalar = 8'h99;
    same.scalar = 8'h99;
    src.scalar = 8'h88;
    #1;
    force s.arr[2] = 8'haa;
    force s.scalar = 8'hbb;
    #1;
    snap = s;
    `checkh(snap.arr[2], 8'haa);
    `checkh(snap.arr[0], 8'h10);
    `checkh(snap.scalar, 8'hbb);
    // Same time step as the force, with no delay in between
    `checkh(via_copy(s), 8'haa);
    grab(s, tout);
    `checkh(tout, 8'haa);
    `checkh((s == same), 1'b0);
    q[0] = s;
    `checkh(q[0].arr[2], 8'haa);
    `checkh(q[0].arr[0], 8'h10);
    // Two whole-struct reads in one statement
    `checkh(((s == same) || (s == q[0])), 1'b1);
    #1;
    `checkh(via_copy(s), 8'haa);
    `checkh((s == same), 1'b0);
    release s.arr[2];
    release s.scalar;
    #1;

    //=======================================================================
    // 2. A bit or part select of an element of an array member
    //=======================================================================
    for (int i = 0; i < 4; ++i) s.arr[i] = 8'h10 + 8'(i);
    s.scalar = 8'h99;
    #1;
    force s.arr[2][3:0] = 4'ha;
    #1;
    `checkh(s.arr[2], 8'h1a);
    `checkh(s.arr[1], 8'h11);
    `checkh(s.scalar, 8'h99);
    // A second force of a disjoint part of the same element coexists with the first
    force s.arr[2][7:4] = 4'hc;
    #1;
    `checkh(s.arr[2], 8'hca);
    release s.arr[2][3:0];
    release s.arr[2][7:4];
    #1;
    `checkh(s.arr[2], 8'hca);

    //=======================================================================
    // 3. A whole plain unpacked array, which is one uniform stride and so needs no
    //     per-leaf targets, and a read of the whole array while an element is forced
    //=======================================================================
    for (int i = 0; i < 4; ++i) begin
      parr[i] = 8'h10 + 8'(i);
      pfill[i] = 8'h30 + 8'(i);
    end
    #1;
    force parr = pfill;
    #1;
    `checkh(parr[0], 8'h30);
    `checkh(parr[2], 8'h32);
    release parr;
    #1;
    `checkh(parr[2], 8'h32);
    force parr[2] = 8'hb9;
    #1;
    psnap = parr;
    `checkh(psnap[2], 8'hb9);
    `checkh(psnap[0], 8'h30);
    release parr[2];
    #1;

    // A bit force inside a whole-array force: the untouched elements keep showing
    // the whole force, and a release of the bits retains them
    force parr = pfill;
    #1;
    force parr[1][3:0] = 4'he;
    #1;
    `checkh(parr[1], 8'h3e);
    `checkh(parr[0], 8'h30);
    `checkh(parr[2], 8'h32);
    release parr[1][3:0];
    #1;
    `checkh(parr[1], 8'h3e);
    `checkh(parr[2], 8'h32);
    release parr;
    #1;

    //=======================================================================
    // 4. A force replaces an earlier force over the range they share, and the
    //     release then keeps that value.  IEEE 1800-2023 10.6.2 does not
    //     describe overlapping force targets, so an aggregate is held to the
    //     same rule as the packed vector checked first here.
    //=======================================================================
    vec = 8'h11;
    #1;
    force vec = 8'h21;
    #1;
    `checkh(vec, 8'h21);
    force vec[3:0] = 4'h5;
    #1;
    `checkh(vec, 8'h25);
    release vec[3:0];
    #1;
    `checkh(vec, 8'h25);
    release vec;
    #1;
    `checkh(vec, 8'h25);

    for (int i = 0; i < 4; ++i) src.arr[i] = 8'h20 + 8'(i);
    src.scalar = 8'h88;
    #1;
    force s = src;
    #1;
    `checkh(s.arr[2], 8'h22);
    force s.arr[2] = 8'h30;
    #1;
    `checkh(s.arr[2], 8'h30);
    release s.arr[2];
    #1;
    `checkh(s.arr[2], 8'h30);
    // The rest of the earlier force is still in effect
    `checkh(s.arr[1], 8'h21);
    `checkh(s.scalar, 8'h88);
    // A whole read sees the released element and the still-forced rest alike
    snap = s;
    `checkh(snap.arr[2], 8'h30);
    `checkh(snap.arr[1], 8'h21);
    // Releasing a leaf the aggregate force still owns punches a hole in it: the leaf
    // keeps its value, a later assignment lands, and whole reads see both
    release s.arr[1];
    #1;
    `checkh(s.arr[1], 8'h21);
    s.arr[1] = 8'h77;
    #1;
    `checkh(s.arr[1], 8'h77);
    snap = s;
    `checkh(snap.arr[1], 8'h77);
    `checkh(snap.arr[3], 8'h23);
    `checkh(snap.scalar, 8'h88);
    release s;
    #1;

    //=======================================================================
    // 5. Aggregate forces nested three structs deep.  Outermost first: each
    //     inner force takes over its subtree, and whole reads and leaf reads
    //     agree while all three are up.  Releasing the middle one keeps the
    //     values it showed, leaves the outer force holding the rest, and lets
    //     a plain assignment land inside the released region.
    //=======================================================================
    n.sub.sub.x = 8'h10;
    n.sub.sub.y = 8'h11;
    n.sub.pad = 8'h12;
    n.pad = 8'h13;
    z2.sub.sub.x = 8'h20;
    z2.sub.sub.y = 8'h21;
    z2.sub.pad = 8'h22;
    z2.pad = 8'h23;
    z1.sub.x = 8'h30;
    z1.sub.y = 8'h31;
    z1.pad = 8'h32;
    z0.x = 8'h40;
    z0.y = 8'h41;
    #1;
    force n = z2;
    force n.sub = z1;
    force n.sub.sub = z0;
    #1;
    nsnap = n;
    `checkh(nsnap.sub.sub.x, 8'h40);
    `checkh(nsnap.sub.sub.y, 8'h41);
    `checkh(nsnap.sub.pad, 8'h32);
    `checkh(nsnap.pad, 8'h23);
    `checkh(n.sub.sub.x, 8'h40);
    `checkh(n.sub.pad, 8'h32);
    `checkh(n.pad, 8'h23);
    // Releasing the middle releases everything under it, retaining the values
    // shown, while the outer force keeps the part it still owns
    release n.sub;
    #1;
    nsnap = n;
    `checkh(nsnap.sub.sub.x, 8'h40);
    `checkh(nsnap.sub.pad, 8'h32);
    `checkh(nsnap.pad, 8'h23);
    n.sub.pad = 8'h77;
    #1;
    `checkh(n.sub.pad, 8'h77);
    nsnap = n;
    `checkh(nsnap.sub.pad, 8'h77);
    `checkh(nsnap.pad, 8'h23);
    release n;
    #1;

    // The other activation order: the outer force, arriving last, takes back
    // the innermost subtree
    force n.sub.sub = z0;
    #1;
    `checkh(n.sub.sub.x, 8'h40);
    force n = z2;
    #1;
    nsnap = n;
    `checkh(nsnap.sub.sub.x, 8'h20);
    `checkh(nsnap.sub.pad, 8'h22);
    `checkh(n.sub.sub.x, 8'h20);
    release n;
    #1;

    // Release retention writes only what the released force owned: with the
    // whole struct forced, release the array member, overwrite it plainly,
    // force one element back, and release the array again.  The second
    // release must keep the plain values, not resurrect the whole force's own
    for (int i = 0; i < 4; ++i) begin
      rt.arr[i] = 8'h10 + 8'(i);
      rtsrc.arr[i] = 8'ha0 + 8'(i);
    end
    rt.tail = 8'h1f;
    rtsrc.tail = 8'haf;
    #1;
    force rt = rtsrc;
    #1;
    release rt.arr;
    #1;
    for (int i = 0; i < 4; ++i) rt.arr[i] = 8'h50 + 8'(i);
    #1;
    force rt.arr[1] = 8'hee;
    #1;
    release rt.arr;
    #1;
    `checkh(rt.arr[0], 8'h50);
    `checkh(rt.arr[1], 8'hee);
    `checkh(rt.arr[2], 8'h52);
    `checkh(rt.arr[3], 8'h53);
    `checkh(rt.tail, 8'haf);
    release rt;
    #1;

    //=======================================================================
    // 6. Ten forces on one variable, which is past what a compiled read
    //     chain carries per leaf, so leaf reads and release retention go
    //     through the whole-value shadow.  The last force wins, a released
    //     element keeps the value it showed, and re-running the same force
    //     statement in a loop shares one force entry and still lands.
    //=======================================================================
    for (int i = 0; i < 10; ++i) begin
      for (int j = 0; j < 4; ++j) m[i].arr[j] = 8'(8'h10 * i + j);
      m[i].scalar = 8'(8'hf0 + i);
    end
    for (int i = 0; i < 4; ++i) s.arr[i] = 8'h10 + 8'(i);
    s.scalar = 8'h99;
    #1;
    force s = m[0];
    force s = m[1];
    force s = m[2];
    force s = m[3];
    force s = m[4];
    force s = m[5];
    force s = m[6];
    force s = m[7];
    force s = m[8];
    force s = m[9];
    #1;
    `checkh(s.arr[2], 8'h92);
    `checkh(s.scalar, 8'hf9);
    snap = s;
    `checkh(snap.arr[1], 8'h91);
    release s.arr[2];
    #1;
    `checkh(s.arr[2], 8'h92);
    s.arr[2] = 8'h55;
    #1;
    `checkh(s.arr[2], 8'h55);
    `checkh(s.scalar, 8'hf9);
    // An earlier of the ten forces re-executes and takes the variable back whole
    force s = m[4];
    #1;
    `checkh(s.arr[2], 8'h42);
    `checkh(s.scalar, 8'hf4);
    release s;
    #1;
    `checkh(s.scalar, 8'hf4);
    // The same force statement re-executed in a loop lands each time
    for (int i = 0; i < 3; ++i) begin
      force s.arr[1] = 8'hd1;
      #1;
      `checkh(s.arr[1], 8'hd1);
      release s.arr[1];
      s.arr[1] = 8'(8'h60 + i);
      #1;
      `checkh(s.arr[1], 8'(8'h60 + i));
    end

    //=======================================================================
    // 7. A one-element unpacked array is still an unpacked aggregate, so its
    //     element and bit-select forces take the slot path and must compile
    //     and run, at one dimension and at a one-by-one multidimensional shape.
    //=======================================================================
    one[5] = 16'h1234;
    #1;
    force one[5][11:4] = 8'hab;
    #1;
    `checkh(one[5], 16'h1ab4);
    release one[5][11:4];
    #1;
    `checkh(one[5], 16'h1ab4);
    onemd[2][7] = 8'h39;
    #1;
    force onemd[2][7] = 8'he4;
    #1;
    `checkh(onemd[2][7], 8'he4);
    release onemd[2][7];
    #1;

    //=======================================================================
    // 8. Releasing an aggregate keeps the value it currently shows, including a
    //     hole an earlier sub-region release punched in it: releasing the whole
    //     must not resurrect the enclosing force's value over that hole.
    //=======================================================================
    hs.y = 16'h1234;
    hs.z = 8'h56;
    hrhs.y = 16'ha000;
    hrhs.z = 8'hbc;
    #1;
    force hs = hrhs;
    force hs.y[7:4] = 4'he;
    #1;
    `checkh(hs.y, 16'ha0e0);
    release hs.y[7:4];
    #1;
    `checkh(hs.y, 16'ha0e0);
    release hs;
    #1;
    `checkh(hs.y, 16'ha0e0);
    `checkh(hs.z, 8'hbc);

    //=======================================================================
    // 9. Recomposing a whole-aggregate force over a non-bitwise single-slot
    //     hole.  An inner force on a real member is one force slot carrying no
    //     bit residue, so the merged value restores it owned-or-raw rather than
    //     bit-blended, and a whole-struct read sees the inner force's value.
    //=======================================================================
    rbs.r = 1.0;
    rbs.a = 8'h11;
    rbsrc.r = 2.5;
    rbsrc.a = 8'haa;
    #1;
    force rbs = rbsrc;
    force rbs.r = 3.0;
    #1;
    rbsnap = rbs;
    `checkr(rbsnap.r, 3.0);
    `checkh(rbsnap.a, 8'haa);
    release rbs.r;
    #1;
    `checkh(rbs.a, 8'haa);
    release rbs;
    #1;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
