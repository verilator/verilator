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
// operand is genuinely enforced by the solver, not silently dropped. Both
// operators are checked, plus a deliberate contradiction (forcing == and
// != against the same non-rand array at once) to prove neither is a no-op.
// Also covers two array shapes this fix must not disturb: a rand-vs-rand
// array comparison (already worked via native SMT array equality) and a
// 3-D non-rand array (the fix's recursion must not be depth-limited to 2-D).

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

module t;
  initial begin
    frame_bothrand bothrand_obj;
    frame_3d d3_obj;
    frame_eq eq_obj;
    frame_neq neq_obj;
    frame_contradiction bad_obj;
    bit [7:0] prev[4][4];
    int ok;
    bit any_diff;

    // rand-vs-rand comparison must keep working (native SMT array equality)
    bothrand_obj = new;
    for (int t = 0; t < 20; t++) begin
      `checkd(bothrand_obj.randomize(), 1)
      `checkd(bothrand_obj.frame != bothrand_obj.other, 1)
    end

    // 3-D non-rand array must force the exact value, same as 2-D
    d3_obj = new;
    `checkd(d3_obj.randomize(), 1)
    `checkd(d3_obj.frame[0][0][0], 8'h01)
    `checkd(d3_obj.frame[0][0][1], 8'h02)
    `checkd(d3_obj.frame[0][1][0], 8'h03)
    `checkd(d3_obj.frame[0][1][1], 8'h04)
    `checkd(d3_obj.frame[1][0][0], 8'h05)
    `checkd(d3_obj.frame[1][0][1], 8'h06)
    `checkd(d3_obj.frame[1][1][0], 8'h07)
    `checkd(d3_obj.frame[1][1][1], 8'h08)

    // '==' against a non-rand array must force the exact value
    eq_obj = new;
    `checkd(eq_obj.randomize(), 1)
    `checkd(eq_obj.frame[0][0], 8'h11)
    `checkd(eq_obj.frame[0][1], 8'h22)
    `checkd(eq_obj.frame[1][0], 8'h33)
    `checkd(eq_obj.frame[1][1], 8'h44)

    // '!=' against a non-rand array must be genuinely enforced every call
    neq_obj = new;
    for (int t = 0; t < 50; t++) begin
      `checkd(neq_obj.randomize(), 1)
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
    `checkd(bad_obj.randomize(), 0)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
