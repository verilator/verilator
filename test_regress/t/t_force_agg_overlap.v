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
//  4. more forces on one variable than a compiled read chain carries, so leaf
//     reads and release retention route through the whole-value shadow, and
//     re-executed identical force statements, which share one force entry,
//  5. one-element unpacked arrays, one- and multi-dimensional, whose element
//     and bit-select forces still take the slot path.
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

module t;

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
  logic [15:0] one[5:5];
  logic [7:0] onemd[2:2][7:7];

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
    // 4. Ten forces on one variable, which is past what a compiled read
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
    // 5. A one-element unpacked array is still an unpacked aggregate, so its
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

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
