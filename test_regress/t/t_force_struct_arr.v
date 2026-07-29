// DESCRIPTION: Verilator: Verilog Test module
//
// Asserts how 'force' and 'release' behave on targets reached through the member
// and element path of an aggregate, per IEEE 1800-2023 10.6.1 and 10.6.2.  An
// element of an unpacked array is a singular reference (6.4), so it is one of
// the left-hand sides 10.6.2 allows, however the array is reached.
//
// Each section below states what it asserts:
//  1. reading the whole struct while an element of an array member is forced,
//  2. forces through nested structs, arrays of structs, multi-dimensional
//     arrays and unpacked unions,
//  3. element widths and array bounds off the word and power-of-two edges,
//     reached through a struct member,
//  4. a scalar member of an array of structs, wherever it sits in the struct,
//  5. a bit or part select of an element of an array member,
//  6. the 'assign' and 'deassign' form, and a force, through an interface,
//  7. a whole plain unpacked array, which is one uniform stride,
//  8. a force replacing an earlier force over the range they share,
//  9. reads reaching a leaf by a run-time index, through a continuous-assign
//     reader of the whole struct, across differing leaf widths, with an
//     intermediate aggregate as the target, and through a union sibling.
//
// The element force itself, its isolation, writes while forced and release
// retention are asserted by t_force_unpacked_struct; a whole-struct force read
// through member paths by t_force_nested_struct; widths, bit selects and packed
// shapes by t_force_unpacked_bitsel, t_force_struct_partial and
// t_force_nested_struct2.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct {
  logic [7:0] arr[4];
  logic [7:0] scalar;
} st_t;

interface Bus;
  st_t s;
endinterface

module t;

  typedef struct {
    logic [7:0] arr[4];
    logic [7:0] tag;
  } inner_t;
  typedef struct {
    inner_t in;
    inner_t ia[2];
    logic [7:0] md[2][3];
    logic [7:0] tail;
  } outer_t;
  typedef union {
    logic [7:0] ua[4];
    logic [7:0] ub[4];
  } uni_t;
  /* verilator lint_off ASCRANGE */
  typedef struct {
    logic [64:0] wide[3];
    logic [1:7] asc[1:3];
  } wid_t;
  /* verilator lint_on ASCRANGE */
  typedef struct {
    logic [7:0] head;
    logic [7:0] arr[4];
  } head_t;
  typedef struct {
    logic [7:0] arr[4];
    logic [7:0] tail;
  } tail_t;
  typedef struct {
    logic [7:0] narrow;
    logic [64:0] wide;
  } mix_t;
  typedef union {
    int ua;
    int ub;
  } uni2_t;

  st_t s;
  st_t src;
  st_t same;
  st_t snap;
  st_t q[2];
  st_t cont_whole;
  outer_t o;
  uni_t u;
  wid_t w;
  head_t sh[3];
  tail_t st[3];
  logic [7:0] tout;
  logic [7:0] drv;
  logic [7:0] parr[4];
  logic [7:0] pfill[4];
  logic [7:0] psnap[4];
  uni2_t u2;
  uni2_t u2copy;
  bit never = 0;
  logic sel;
  logic [7:0] vec;
  mix_t mix;
  mix_t mix_src;
  int idx;
  logic [7:0] cont_whole_arr2;
  logic [7:0] cont_whole_scalar;

  Bus bus ();

  // Reads the struct whole, so it takes the shadow rather than a per-leaf read
  assign cont_whole = s;
  assign cont_whole_arr2 = cont_whole.arr[2];
  assign cont_whole_scalar = cont_whole.scalar;

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
    // 2. Nested structs, arrays of structs, multi-dimensional arrays, unions
    //=======================================================================
    for (int i = 0; i < 4; ++i) o.in.arr[i] = 8'h10 + 8'(i);
    o.in.tag = 8'h1f;
    for (int i = 0; i < 2; ++i)
      for (int k = 0; k < 4; ++k) o.ia[i].arr[k] = 8'h40 + 8'(i * 16 + k);
    o.ia[0].tag = 8'h50;
    o.ia[1].tag = 8'h51;
    for (int i = 0; i < 2; ++i)
      for (int k = 0; k < 3; ++k) o.md[i][k] = 8'h60 + 8'(i * 16 + k);
    o.tail = 8'h7f;
    for (int i = 0; i < 4; ++i) u.ua[i] = 8'h80 + 8'(i);
    #1;

    force o.in.arr[2] = 8'ha1;
    force o.ia[1].arr[3] = 8'ha2;
    force o.md[1][2] = 8'ha3;
    force u.ua[1] = 8'ha4;
    #1;
    `checkh(o.in.arr[2], 8'ha1);
    `checkh(o.in.arr[1], 8'h11);
    `checkh(o.in.tag, 8'h1f);
    `checkh(o.ia[1].arr[3], 8'ha2);
    `checkh(o.ia[1].arr[2], 8'h52);
    `checkh(o.ia[0].arr[3], 8'h43);
    `checkh(o.md[1][2], 8'ha3);
    `checkh(o.md[1][1], 8'h71);
    `checkh(o.md[0][2], 8'h62);
    `checkh(o.tail, 8'h7f);
    `checkh(u.ua[1], 8'ha4);
    `checkh(u.ua[0], 8'h80);

    release o.in.arr[2];
    release o.ia[1].arr[3];
    release o.md[1][2];
    release u.ua[1];
    #1;
    `checkh(o.in.arr[2], 8'ha1);
    `checkh(o.ia[1].arr[3], 8'ha2);
    `checkh(o.md[1][2], 8'ha3);
    `checkh(u.ua[1], 8'ha4);
    o.in.arr[2] = 8'hb1;
    o.md[1][2] = 8'hb3;
    #1;
    `checkh(o.in.arr[2], 8'hb1);
    `checkh(o.md[1][2], 8'hb3);

    //=======================================================================
    // 3. Element widths and array bounds off the word and power-of-two edges,
    //    reached through a struct member
    //=======================================================================
    for (int i = 0; i < 3; ++i) w.wide[i] = 65'h1_0000_0000_0000_0000 + 65'(i);
    for (int i = 1; i <= 3; ++i) w.asc[i] = 7'h20 + 7'(i);
    #1;
    force w.wide[1] = 65'h1_dead_beef_feed_face;
    force w.asc[2] = 7'h2a;
    #1;
    `checkh(w.wide[1], 65'h1_dead_beef_feed_face);
    `checkh(w.wide[0], 65'h1_0000_0000_0000_0000);
    `checkh(w.asc[2], 7'h2a);
    `checkh(w.asc[1], 7'h21);
    `checkh(w.asc[3], 7'h23);
    release w.wide[1];
    release w.asc[2];
    #1;
    `checkh(w.wide[1], 65'h1_dead_beef_feed_face);

    //=======================================================================
    // 4. A scalar member of an array of structs, wherever it sits in the struct
    //=======================================================================
    for (int i = 0; i < 3; ++i) begin
      sh[i].head = 8'h70 + 8'(i);
      st[i].tail = 8'h70 + 8'(i);
      for (int k = 0; k < 4; ++k) begin
        sh[i].arr[k] = 8'h10 + 8'(i * 16 + k);
        st[i].arr[k] = 8'h10 + 8'(i * 16 + k);
      end
    end
    #1;
    force sh[1].head = 8'hbb;
    force st[1].tail = 8'hbb;
    #1;
    `checkh(sh[1].head, 8'hbb);
    `checkh(st[1].tail, 8'hbb);
    `checkh(sh[0].head, 8'h70);
    `checkh(st[0].tail, 8'h70);
    `checkh(sh[2].head, 8'h72);
    `checkh(st[2].tail, 8'h72);
    `checkh(sh[1].arr[2], 8'h22);
    `checkh(st[1].arr[2], 8'h22);
    release sh[1].head;
    release st[1].tail;
    #1;
    `checkh(sh[1].head, 8'hbb);
    `checkh(st[1].tail, 8'hbb);

    //=======================================================================
    // 5. A bit or part select of an element of an array member
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
    // 6. The 'assign' and 'deassign' form, and a force, through an interface instance
    //=======================================================================
    for (int i = 0; i < 4; ++i) bus.s.arr[i] = 8'h10 + 8'(i);
    drv = 8'haa;
    #1;
    /* verilator lint_off IEEEMAYDEPRECATE */
    assign bus.s.arr[2] = drv;
    #1;
    `checkh(bus.s.arr[2], 8'haa);
    `checkh(bus.s.arr[1], 8'h11);
    // A procedural continuous assignment tracks its right-hand side
    drv = 8'hcc;
    #1;
    `checkh(bus.s.arr[2], 8'hcc);
    deassign bus.s.arr[2];
    #1;
    bus.s.arr[2] = 8'h55;
    #1;
    // The stale right-hand side must no longer drive the element
    drv = 8'hdd;
    #1;
    `checkh(bus.s.arr[2], 8'h55);
    /* verilator lint_on IEEEMAYDEPRECATE */

    force bus.s.arr[2] = 8'hee;
    #1;
    `checkh(bus.s.arr[2], 8'hee);
    `checkh(bus.s.arr[1], 8'h11);
    release bus.s.arr[2];
    #1;
    `checkh(bus.s.arr[2], 8'hee);

    //=======================================================================
    // 7. A whole plain unpacked array, which is one uniform stride and so needs no
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

    //=======================================================================
    // 8. A force replaces an earlier force over the range they share, and the
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
    release s;
    #1;

    //=======================================================================
    // 9. Reads that reach a leaf by a route the sections above do not take:
    //     a run-time element index through a member path, a continuous-assign
    //     reader of the whole struct, a struct whose leaves differ in width,
    //     an intermediate aggregate as the force target, and the other member
    //     of a union whose storage is shared but whose slots are not.
    //=======================================================================
    for (int i = 0; i < 4; ++i) s.arr[i] = 8'h10 + 8'(i);
    s.scalar = 8'h99;
    idx = 2;
    #1;
    force s.arr[2] = 8'hf1;
    #1;
    // Run-time index, so the slot ordinal is computed rather than folded
    `checkh(s.arr[idx], 8'hf1);
    idx = 1;
    `checkh(s.arr[idx], 8'h11);
    // A continuous-assign reader of the whole struct
    `checkh(cont_whole_arr2, 8'hf1);
    `checkh(cont_whole_scalar, 8'h99);
    release s.arr[2];
    #1;

    // Leaves of differing width, forced as a whole struct
    mix_src.narrow = 8'h5a;
    mix_src.wide = 65'h1_9999_8888_7777_6666;
    mix.narrow = 8'h01;
    mix.wide = 65'h0;
    #1;
    force mix = mix_src;
    #1;
    `checkh(mix.narrow, 8'h5a);
    `checkh(mix.wide, 65'h1_9999_8888_7777_6666);
    release mix;
    #1;
    `checkh(mix.wide, 65'h1_9999_8888_7777_6666);

    // An intermediate aggregate as the target
    force o.in = o.ia[0];
    #1;
    `checkh(o.in.arr[2], 8'h42);
    `checkh(o.in.tag, 8'h50);
    `checkh(o.ia[1].arr[2], 8'h52);
    release o.in;
    #1;
    `checkh(o.in.arr[2], 8'h42);

    // Union members are tracked apart, so a force through one member is not visible
    // through the other even though the two share storage.  Pinned here as the
    // behaviour this change leaves in place, not as a guarantee.
    for (int i = 0; i < 4; ++i) u.ua[i] = 8'h80 + 8'(i);
    #1;
    force u.ua[1] = 8'hc7;
    #1;
    `checkh(u.ua[1], 8'hc7);
    `checkh(u.ub[1], 8'h81);
    release u.ua[1];
    #1;
    `checkh(u.ua[1], 8'hc7);

    // Overlaid union members: a copy of the whole union carries the forced value
    // through, as the two members are the same storage
    u2.ua = 1;
    #1;
    force u2.ua = 2;
    // A force that never executes leaves the overlaid member untouched
    if (never) force u2.ub = 3;
    #1;
    u2copy = u2;
    `checkh(u2copy.ua, 2);
    `checkh(u2copy.ub, 2);
    release u2.ua;
    #1;

    // A whole-struct force from an expression, which is evaluated per member and so
    // must be free of side effects
    sel = 1'b1;
    src.scalar = 8'hc1;
    for (int i = 0; i < 4; ++i) src.arr[i] = 8'hd0 + 8'(i);
    #1;
    force s = sel ? src : same;
    #1;
    `checkh(s.scalar, 8'hc1);
    `checkh(s.arr[2], 8'hd2);
    release s;
    #1;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
