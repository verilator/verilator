// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test that a whole-array '=='/'!=' constraint against a non-rand array
// operand is genuinely enforced by the solver, not silently dropped.

class frame_bothrand;
  rand bit [7:0] frame[2][2];
  rand bit [7:0] other[2][2];
  constraint c { frame != other; }
endclass

// Both the array and the index are rand -- this must keep going through
// native SMT array equality (a rand index used here is not the "can't
// evaluate a non-rand operand at solve time" problem an index into a
// non-rand array runs into, since there's no non-rand value being frozen).
class frame_bothrand_randidx;
  rand int idx;
  rand bit [7:0] cube[4][2];
  rand bit [7:0] probe[2];
  constraint ci { idx inside {[0:3]}; }
  constraint c { probe == cube[idx]; }
endclass

class frame_3d;
  rand bit [7:0] frame[2][2][2];
  bit [7:0] target[2][2][2];
  constraint c { frame == target; }
  function new();
    target[0][0][0] = 8'h01;
    target[0][0][1] = 8'h02;
    target[0][1][0] = 8'h03;
    target[0][1][1] = 8'h04;
    target[1][0][0] = 8'h05;
    target[1][0][1] = 8'h06;
    target[1][1][0] = 8'h07;
    target[1][1][1] = 8'h08;
  endfunction
endclass

// Same, but 'frame'/'target' have a non-zero declared range ([1:4]), and
// the non-rand operand is written first ('target == frame') to confirm
// operand order doesn't matter.
class frame_nonzero_base;
  rand bit [7:0] frame[1:4];
  bit [7:0] target[1:4];
  constraint c { target == frame; }
  function new();
    target[1] = 8'h11;
    target[2] = 8'h22;
    target[3] = 8'h33;
    target[4] = 8'h44;
  endfunction
endclass

// Same, reached via a member select (holder.target).
class Holder;
  bit [7:0] target[2][2];
  function new();
    target[0][0] = 8'h11;
    target[0][1] = 8'h22;
    target[1][0] = 8'h33;
    target[1][1] = 8'h44;
  endfunction
endclass

class frame_via_member;
  rand bit [7:0] frame[2][2];
  Holder holder;
  constraint c { frame == holder.target; }
  function new();
    holder = new;
  endfunction
endclass

// Same non-rand member access, but the handle itself is rand -- a class
// member has its own rand qualifier independent of its handle, unlike a
// struct field, which shares its parent's.
class frame_via_rand_handle;
  rand bit [7:0] frame[2][2];
  rand Holder holder;
  constraint c { frame == holder.target; }
  function new();
    holder = new;
  endfunction
endclass

// Mirror of frame_via_rand_handle: the member is declared rand, but the
// handle reaching it isn't -- since the handle is never included in this
// randomize() call, the member's value is fixed, same as any other
// non-rand operand.
class RandMember;
  rand bit [7:0] target[2][2];
  function new();
    target[0][0] = 8'h55;
    target[0][1] = 8'h66;
    target[1][0] = 8'h77;
    target[1][1] = 8'h88;
  endfunction
endclass

class frame_via_nonrand_handle_rand_member;
  rand bit [7:0] frame[2][2];
  RandMember holder;
  constraint c { frame == holder.target; }
  function new();
    holder = new;
  endfunction
endclass

// Non-rand side reached via a struct field (StructSel), not a class member
// (MemberSel) -- a plain, non-rand struct-typed variable whose array field
// is the whole-array comparison operand.
typedef struct {
  bit [7:0] arr[2];
} plain_struct_t;
class frame_via_struct_field;
  rand bit [7:0] probe[2];
  plain_struct_t sv;
  constraint c { probe == sv.arr; }
  function new();
    sv.arr[0] = 8'h81;
    sv.arr[1] = 8'h82;
  endfunction
endclass

// Rand side reached through a two-level chain, a class member (MemberSel)
// that is itself a struct field (StructSel) -- both the handle and the
// struct-typed member it holds are rand, so the whole chain shares that
// rand-ness down to the array field.
class HolderStruct;
  rand plain_struct_t sv;
endclass
class frame_via_rand_handle_struct;
  rand HolderStruct h;
  bit [7:0] target[2];
  constraint c { h.sv.arr == target; }
  function new();
    h = new;
    target[0] = 8'h91;
    target[1] = 8'h92;
  endfunction
endclass

// An odd element count -- the balanced-tree reduction's carry-forward
// path (an unpaired last element at a given level) only triggers for an
// odd number of remaining nodes, never exercised by an even-sized array.
class frame_odd_count;
  rand bit [7:0] frame[3];
  bit [7:0] target[3];
  constraint c { frame == target; }
  function new();
    target[0] = 8'hA1;
    target[1] = 8'hA2;
    target[2] = 8'hA3;
  endfunction
endclass

// Rand side as a constant-indexed slice of a larger array (cube[0]).
class frame_rand_slice;
  rand bit [7:0] cube[2][2][2];
  bit [7:0] target[2][2];
  constraint c { cube[0] == target; }
  function new();
    target[0][0] = 8'h01;
    target[0][1] = 8'h02;
    target[1][0] = 8'h03;
    target[1][1] = 8'h04;
  endfunction
endclass

class frame_neq;
  rand bit [7:0] frame[4][4];
  bit [7:0] last_frame[4][4];
  bit has_prev;
  constraint c { if (has_prev) frame != last_frame; }
  function void post_randomize();
    last_frame = frame;
    has_prev = 1;
  endfunction
endclass

class frame_contradiction;
  rand bit [7:0] frame[2][2];
  bit [7:0] target[2][2];
  constraint c1 { frame == target; }
  constraint c2 { frame != target; }
  function new();
    target[0][0] = 8'h11;
    target[0][1] = 8'h22;
    target[1][0] = 8'h33;
    target[1][1] = 8'h44;
  endfunction
endclass

// Both operands are member selects on array-indexed elements of the same
// rand array (x[0].a vs x[1].a); the root-variable resolver must recurse
// through the index to find 'x', not just the member select itself.
typedef struct {
  bit [7:0] a[2];
} s_t;
class member_of_rand_array;
  rand s_t x[2];
  constraint c { x[0].a != x[1].a; }
endclass

// Rand array indexed by a plain (non-rand) variable, then whole-compared
// against a non-rand target -- the index itself must never be mistaken
// for part of the rand comparison operand.
class frame_nonrand_index;
  rand bit [7:0] frame[3][2];
  bit [7:0] target[2];
  int idx;
  constraint c { frame[idx] == target; }
  function new();
    idx = 1;
    target[0] = 8'h21;
    target[1] = 8'h22;
  endfunction
endclass

// An array large enough that a left-deep AstLogAnd chain (one per element)
// overflows the stack in a later recursive pass -- the reduction has to
// stay a bounded (balanced-tree) depth well before reaching this size.
class frame_large;
  rand bit [7:0] frame[4096];
  bit [7:0] target[4096];
  constraint c { frame == target; }
  function new();
    for (int i = 0; i < 4096; i++) target[i] = i[7:0];
  endfunction
endclass

module t;
  initial begin
    frame_bothrand bothrand_obj;
    frame_bothrand_randidx randidx_bothrand_obj;
    frame_3d d3_obj;
    frame_nonzero_base nzbase_obj;
    frame_via_member member_obj;
    frame_via_rand_handle randhandle_obj;
    frame_via_nonrand_handle_rand_member nonrandhandle_obj;
    frame_via_struct_field structfield_obj;
    frame_via_rand_handle_struct randhandlestruct_obj;
    frame_odd_count odd_obj;
    frame_rand_slice slice_obj;
    frame_neq neq_obj;
    frame_contradiction bad_obj;
    member_of_rand_array member_idx_obj;
    frame_nonrand_index nonrand_idx_obj;
    frame_large large_obj;
    bit [7:0] prev[4][4];
    bit [7:0] prev_cube1[2][2];
    int randomize_result;
    bit any_diff;

    // rand-vs-rand comparison must keep working (native SMT array equality)
    bothrand_obj = new;
    for (int t = 0; t < 20; t++) begin
      randomize_result = bothrand_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(bothrand_obj.frame != bothrand_obj.other, 1);
    end

    // Both operand and index rand must keep solving correctly (native SMT),
    // and the index must actually vary across draws, not just default to 0.
    randidx_bothrand_obj = new;
    any_diff = 0;
    for (int t = 0; t < 20; t++) begin
      randomize_result = randidx_bothrand_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(randidx_bothrand_obj.probe, randidx_bothrand_obj.cube[randidx_bothrand_obj.idx]);
      if (randidx_bothrand_obj.idx != 0) any_diff = 1;
    end
    if (!any_diff) begin
      $write("%%Error: idx never varied across 20 draws\n");
      `stop;
    end

    // 3-D non-rand array must force the exact value, same as 2-D
    d3_obj = new;
    randomize_result = d3_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(d3_obj.frame[0][0][0], 8'h01);
    `checkd(d3_obj.frame[0][0][1], 8'h02);
    `checkd(d3_obj.frame[0][1][0], 8'h03);
    `checkd(d3_obj.frame[0][1][1], 8'h04);
    `checkd(d3_obj.frame[1][0][0], 8'h05);
    `checkd(d3_obj.frame[1][0][1], 8'h06);
    `checkd(d3_obj.frame[1][1][0], 8'h07);
    `checkd(d3_obj.frame[1][1][1], 8'h08);

    // A non-zero-based declared array range must force the exact value
    nzbase_obj = new;
    randomize_result = nzbase_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(nzbase_obj.frame[1], 8'h11);
    `checkd(nzbase_obj.frame[2], 8'h22);
    `checkd(nzbase_obj.frame[3], 8'h33);
    `checkd(nzbase_obj.frame[4], 8'h44);

    // Non-rand array reached via a member select must force the exact value
    member_obj = new;
    randomize_result = member_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(member_obj.frame[0][0], 8'h11);
    `checkd(member_obj.frame[0][1], 8'h22);
    `checkd(member_obj.frame[1][0], 8'h33);
    `checkd(member_obj.frame[1][1], 8'h44);

    // Same member access, but through a rand handle -- the member's own
    // rand qualifier (not rand) must govern, not the handle's (rand).
    randhandle_obj = new;
    randomize_result = randhandle_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(randhandle_obj.frame[0][0], 8'h11);
    `checkd(randhandle_obj.frame[0][1], 8'h22);
    `checkd(randhandle_obj.frame[1][0], 8'h33);
    `checkd(randhandle_obj.frame[1][1], 8'h44);

    // Mirror case: member is rand, but the handle reaching it isn't -- the
    // handle's own (not rand) qualifier must govern here, not the member's.
    nonrandhandle_obj = new;
    randomize_result = nonrandhandle_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(nonrandhandle_obj.frame[0][0], 8'h55);
    `checkd(nonrandhandle_obj.frame[0][1], 8'h66);
    `checkd(nonrandhandle_obj.frame[1][0], 8'h77);
    `checkd(nonrandhandle_obj.frame[1][1], 8'h88);

    // Non-rand side reached through a struct field must force the exact
    // value.
    structfield_obj = new;
    randomize_result = structfield_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(structfield_obj.probe[0], 8'h81);
    `checkd(structfield_obj.probe[1], 8'h82);

    // Rand side reached through a rand handle's rand struct-typed member
    // must force the exact value.
    randhandlestruct_obj = new;
    randomize_result = randhandlestruct_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(randhandlestruct_obj.h.sv.arr[0], 8'h91);
    `checkd(randhandlestruct_obj.h.sv.arr[1], 8'h92);

    // An odd-sized array must still force every element correctly.
    odd_obj = new;
    randomize_result = odd_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(odd_obj.frame[0], 8'hA1);
    `checkd(odd_obj.frame[1], 8'hA2);
    `checkd(odd_obj.frame[2], 8'hA3);

    // A constant-indexed slice of a larger rand array, used as a whole
    // comparison operand, must force the exact value on that slice -- and
    // leave the rest of the same rand array (cube[1], untouched by the
    // constraint) genuinely random, not incidentally pinned too.
    slice_obj = new;
    any_diff = 0;
    for (int t = 0; t < 20; t++) begin
      randomize_result = slice_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(slice_obj.cube[0][0][0], 8'h01);
      `checkd(slice_obj.cube[0][0][1], 8'h02);
      `checkd(slice_obj.cube[0][1][0], 8'h03);
      `checkd(slice_obj.cube[0][1][1], 8'h04);
      if (t > 0 && slice_obj.cube[1] != prev_cube1) any_diff = 1;
      prev_cube1 = slice_obj.cube[1];
    end
    if (!any_diff) begin
      $write("%%Error: cube[1] never varied across 20 draws\n");
      `stop;
    end

    // '!=' against a non-rand array must be genuinely enforced every call
    neq_obj = new;
    for (int t = 0; t < 50; t++) begin
      randomize_result = neq_obj.randomize();
      `checkd(randomize_result, 1);
      if (t > 0) begin
        any_diff = 0;
        for (int i = 0; i < 4; i++)
          for (int j = 0; j < 4; j++)
            if (neq_obj.frame[i][j] != prev[i][j]) any_diff = 1;
        if (!any_diff) begin
          $write("%%Error: frame %0d identical to frame %0d\n", t, t - 1);
          `stop;
        end
      end
      prev = neq_obj.frame;
    end

    // A simultaneous '==' and '!=' against the same non-rand array must
    // correctly fail, proving neither operator is being silently ignored.
    bad_obj = new;
    randomize_result = bad_obj.randomize();
    `checkd(randomize_result, 0);

    // Still rand-vs-rand; must not get misrouted into the expansion path.
    member_idx_obj = new;
    randomize_result = member_idx_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(member_idx_obj.x[0].a != member_idx_obj.x[1].a, 1);

    // A rand array indexed by a plain non-rand variable, whole-compared
    // against a non-rand target, must force the exact value at that row.
    nonrand_idx_obj = new;
    randomize_result = nonrand_idx_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(nonrand_idx_obj.frame[1][0], 8'h21);
    `checkd(nonrand_idx_obj.frame[1][1], 8'h22);

    // A large array's elementwise reduction must not overflow the stack,
    // and must still force every element to its expected value.
    large_obj = new;
    randomize_result = large_obj.randomize();
    `checkd(randomize_result, 1);
    any_diff = 0;
    for (int i = 0; i < 4096; i++) begin
      if (large_obj.frame[i] !== i[7:0]) any_diff = 1;
    end
    if (any_diff) begin
      $write("%%Error: frame_large did not force the expected values\n");
      `stop;
    end

    // std::randomize() arguments are rand for the call regardless of their
    // own declared qualifier -- the same elementwise expansion must apply
    // there too, not just to a class's own rand members.
    begin
      bit [7:0] sa[2], sb[2], sc[2];
      int std_result;
      sb[0] = 8'hAA;
      sb[1] = 8'hBB;
      std_result = std::randomize(sa, sc) with { sa == sc; };
      `checkd(std_result, 1);
      `checkd(sa == sc, 1);
      std_result = std::randomize(sa) with { sa == sb; };
      `checkd(std_result, 1);
      `checkd(sa[0], 8'hAA);
      `checkd(sa[1], 8'hBB);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
