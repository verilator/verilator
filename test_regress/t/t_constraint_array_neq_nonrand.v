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

// Same, but 'frame'/'target' have a non-zero declared range ([1:4]).
class frame_nonzero_base;
  rand bit [7:0] frame[1:4];
  bit [7:0] target[1:4];
  constraint c { frame == target; }
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

class frame_eq;
  rand bit [7:0] frame[2][2];
  bit [7:0] target[2][2];
  constraint c { frame == target; }
  function new();
    target[0][0] = 8'h11;
    target[0][1] = 8'h22;
    target[1][0] = 8'h33;
    target[1][1] = 8'h44;
  endfunction
endclass

// Non-rand operand written first: 'target == frame' instead of the usual
// 'frame == target'.
class frame_swapped;
  rand bit [7:0] frame[2][2];
  bit [7:0] target[2][2];
  constraint c { target == frame; }
  function new();
    target[0][0] = 8'h11;
    target[0][1] = 8'h22;
    target[1][0] = 8'h33;
    target[1][1] = 8'h44;
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

module t;
  initial begin
    frame_bothrand bothrand_obj;
    frame_3d d3_obj;
    frame_nonzero_base nzbase_obj;
    frame_via_member member_obj;
    frame_rand_slice slice_obj;
    frame_eq eq_obj;
    frame_swapped swapped_obj;
    frame_neq neq_obj;
    frame_contradiction bad_obj;
    member_of_rand_array member_idx_obj;
    bit [7:0] prev[4][4];
    int randomize_result;
    bit any_diff;

    // rand-vs-rand comparison must keep working (native SMT array equality)
    bothrand_obj = new;
    for (int t = 0; t < 20; t++) begin
      randomize_result = bothrand_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(bothrand_obj.frame != bothrand_obj.other, 1);
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

    // A constant-indexed slice of a larger rand array, used as a whole
    // comparison operand, must force the exact value too
    slice_obj = new;
    randomize_result = slice_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(slice_obj.cube[0][0][0], 8'h01);
    `checkd(slice_obj.cube[0][0][1], 8'h02);
    `checkd(slice_obj.cube[0][1][0], 8'h03);
    `checkd(slice_obj.cube[0][1][1], 8'h04);

    // '==' against a non-rand array must force the exact value
    eq_obj = new;
    randomize_result = eq_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(eq_obj.frame[0][0], 8'h11);
    `checkd(eq_obj.frame[0][1], 8'h22);
    `checkd(eq_obj.frame[1][0], 8'h33);
    `checkd(eq_obj.frame[1][1], 8'h44);

    // '==' must force the exact value with operands in either order
    swapped_obj = new;
    randomize_result = swapped_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(swapped_obj.frame[0][0], 8'h11);
    `checkd(swapped_obj.frame[0][1], 8'h22);
    `checkd(swapped_obj.frame[1][0], 8'h33);
    `checkd(swapped_obj.frame[1][1], 8'h44);

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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
