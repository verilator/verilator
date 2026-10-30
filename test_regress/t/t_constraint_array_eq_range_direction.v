// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Whole-array '=='/'!=' must compare by declared position, not raw
// storage index, when the two operands' declared ranges run opposite.

// Both operands rand, opposite direction, '!=': the two arrays must never
// come out procedurally equal, matching what the constraint asked for.
class both_rand_opp_dir;
  rand bit [3:0] frame[0:1];
  rand bit [3:0] target[1:0];
  constraint c { frame != target; }
endclass

// Both operands rand, opposite direction, '==': forces frame to known
// values, then checks target's declared-position-matched elements (not
// its raw storage slots) actually received them.
class both_rand_opp_dir_eq;
  rand bit [3:0] frame[0:1];
  rand bit [3:0] target[1:0];
  constraint cf { frame[0] == 4'd5; frame[1] == 4'd9; }
  constraint c { frame == target; }
endclass

// Both operands rand, same (descending) direction: must keep going
// through the native SMT array-equality fast path, unaffected.
class both_rand_same_dir;
  rand bit [3:0] frame[1:0];
  rand bit [3:0] target[1:0];
  constraint c { frame != target; }
endclass

// Same position-pairing requirement, but with one operand non-rand.
class mixed_rand_opp_dir;
  rand bit [3:0] frame[0:1];
  bit [3:0] target[1:0];
  constraint c { frame == target; }
  function new();
    target[1] = 4'd5;
    target[0] = 4'd9;
  endfunction
endclass

// Same as mixed_rand_opp_dir, with the lhs (rand) side's declared range
// flipped to descending instead of ascending.
class mixed_rand_opp_dir_lhs_desc;
  rand bit [3:0] frame[1:0];
  bit [3:0] target[0:1];
  constraint c { frame == target; }
  function new();
    target[0] = 4'd5;
    target[1] = 4'd9;
  endfunction
endclass

// Both dimensions of a 2-D array run opposite directions between the two
// operands, at both the outer and inner level -- exercises the recursive
// per-level fix, not just the top dimension.
class nested_opp_dir;
  rand bit [3:0] cube[0:1][0:1];
  rand bit [3:0] other[1:0][1:0];
  constraint cf {
    cube[0][0] == 4'd1; cube[0][1] == 4'd2;
    cube[1][0] == 4'd3; cube[1][1] == 4'd4;
  }
  constraint c { cube == other; }
endclass

module t;
  initial begin
    both_rand_opp_dir opp_dir_obj;
    both_rand_opp_dir_eq opp_dir_eq_obj;
    both_rand_same_dir same_dir_obj;
    mixed_rand_opp_dir mixed_obj;
    mixed_rand_opp_dir_lhs_desc mixed_lhs_desc_obj;
    nested_opp_dir nested_obj;
    int randomize_result;

    // Never satisfiable as procedurally equal, every draw.
    opp_dir_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = opp_dir_obj.randomize();
      `checkd(randomize_result, 1);
      if (opp_dir_obj.frame == opp_dir_obj.target) begin
        $write("%%Error: opp_dir: solver said != but procedural == is TRUE: f0=%0d f1=%0d t0=%0d t1=%0d\n",
               opp_dir_obj.frame[0], opp_dir_obj.frame[1], opp_dir_obj.target[0],
               opp_dir_obj.target[1]);
        `stop;
      end
    end

    // frame[0]=5 (declared position 0) must land in target's declared
    // position 0, which for target[1:0] is target[1] -- not target[0].
    opp_dir_eq_obj = new;
    randomize_result = opp_dir_eq_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(opp_dir_eq_obj.target[1], 4'd5);
    `checkd(opp_dir_eq_obj.target[0], 4'd9);

    same_dir_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = same_dir_obj.randomize();
      `checkd(randomize_result, 1);
      if (same_dir_obj.frame == same_dir_obj.target) begin
        $write("%%Error: same_dir: solver said != but procedural == is TRUE\n");
        `stop;
      end
    end

    mixed_obj = new;
    randomize_result = mixed_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(mixed_obj.frame[0], 4'd5);
    `checkd(mixed_obj.frame[1], 4'd9);

    mixed_lhs_desc_obj = new;
    randomize_result = mixed_lhs_desc_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(mixed_lhs_desc_obj.frame[1], 4'd5);
    `checkd(mixed_lhs_desc_obj.frame[0], 4'd9);

    nested_obj = new;
    randomize_result = nested_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(nested_obj.other[1][1], 4'd1);
    `checkd(nested_obj.other[1][0], 4'd2);
    `checkd(nested_obj.other[0][1], 4'd3);
    `checkd(nested_obj.other[0][0], 4'd4);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
