// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test transition bins: simple 2-value, 3-value sequences, array bins,
// and multi-value items in transition steps.

module t;
  logic [2:0] state;

  covergroup cg;
    // Simple 2-value transitions
    cp_trans2: coverpoint state {
      bins trans1 = (0 => 1);
      bins trans2 = (1 => 2);
      bins trans3 = (2 => 3);
    }
    // 3-value sequence transitions
    cp_trans3: coverpoint state {
      bins seq_a = (0 => 1 => 2);
      bins seq_b = (2 => 3 => 4);
    }
    // Array bins: creates a separate bin per listed transition
    cp_array: coverpoint state {
      bins arr[] = (0 => 1), (1 => 2), (2 => 3);
    }
    // Multi-value item (comma list) in transition: matches 1 or 2 in second step
    cp_multi_item: coverpoint state {
      bins multi = (0 => 1, 2);  // second element is a two-value list
    }
    // Repetition-type bins: exercises GOTO and NONCONS repTypes in the AST dump
    cp_reptype: coverpoint state {
      bins goto_bin = (0 => 1 [->2]);    // GOTO repetition, treated as simple (0=>1) match
      bins noncons_bin = (2 [=1] => 3);  // NONCONS repetition, treated as simple (2=>3) match
    }
  endgroup

  cg cg_inst = new;

  initial begin
    // Drive sequence 0->1->2->3->4 which hits all bins
    state = 0; cg_inst.sample();
    state = 1; cg_inst.sample();  // 0=>1: trans1, seq_a pos1, arr[0=>1], multi
    state = 2; cg_inst.sample();  // 1=>2: trans2, seq_a done, arr[1=>2]
    state = 3; cg_inst.sample();  // 2=>3: trans3, seq_b pos1, arr[2=>3]
    state = 4; cg_inst.sample();  // 3=>4: seq_b done

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
