// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class ClsA;
  rand logic member_a;
  randc bit [1:0] member_rc;
endclass

class ClsB;
  rand ClsA member_b;
  rand ClsA inner_b[int];

  function new;
    member_b = new;
  endfunction
endclass

class ClsC;
  bit enable_c;
  rand ClsB member_c[int];

  // Nested member access through the foreach iterator. The registration of the
  // constrained sub-object must stay inside the loop body because it references
  // the loop index (regression: it used to be hoisted outside, leaving a
  // dangling reference after task inlining deleted the index).
  constraint constraint_c {
    foreach (member_c[i]) {
      enable_c == 0 -> member_c[i].member_b.member_a == 1'b1;
    }
  }

  // Nested foreach whose inner body references both loop indices.
  constraint constraint_nested {
    foreach (member_c[i]) {
      foreach (member_c[i].inner_b[j]) {
        member_c[i].inner_b[j].member_a == 1'b1;
      }
    }
  }

  // Fixed index inside a foreach: the constrained sub-object does NOT reference
  // the loop iterator, so its registration stays outside the loop body.
  constraint constraint_fixed {
    foreach (member_c[i]) {
      member_c[0].member_b.member_a == 1'b1;
    }
  }

  // randc sub-object reached through the loop iterator: its cyclic-tracking
  // registration also references the loop index and must stay in the loop body.
  constraint constraint_randc {
    foreach (member_c[i]) {
      member_c[i].member_b.member_rc < 3;
    }
  }

  function new;
    for (int k = 0; k < 3; k++) begin
      ClsB item = new;
      ClsA a0 = new;
      ClsA a1 = new;
      item.inner_b[0] = a0;
      item.inner_b[1] = a1;
      member_c[k] = item;
    end
  endfunction
endclass

module t;
  ClsC obj_c = new;

  initial begin
    int rand_ok;
    obj_c.enable_c = 0;
    repeat (20) begin
      rand_ok = obj_c.randomize();
      `checkd(rand_ok, 1)
      // Every array element must satisfy the loop-index-dependent constraints.
      foreach (obj_c.member_c[i]) begin
        `checkd(obj_c.member_c[i].member_b.member_a, 1'b1)
        if (obj_c.member_c[i].member_b.member_rc >= 3) $stop;
        foreach (obj_c.member_c[i].inner_b[j]) begin
          `checkd(obj_c.member_c[i].inner_b[j].member_a, 1'b1)
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
