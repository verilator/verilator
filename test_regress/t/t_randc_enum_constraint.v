// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test that randc enum variables with user constraints only produce
// valid enum members (not arbitrary bitvector values).

module t;

  typedef enum bit [2:0] {
    RED = 0,
    GREEN = 1,
    BLUE = 2,
    WHITE = 3,
    BLACK = 4
  } color_t;

  class ColorClass;
    randc color_t color;
    constraint c_no_dark {color != BLACK;}
  endclass

  // Test with all enum values allowed (no exclusion constraint)
  class AllColorsClass;
    randc color_t color;
    constraint c_range {color <= WHITE;}
  endclass

  initial begin
    ColorClass c;
    AllColorsClass ac;
    int color_seen[5];
    int first_seq, all_same, this_seq;

    // Test 1: randc enum with exclusion constraint
    // Values must be valid enum members (0-4) and not BLACK (4)
    c = new;
    repeat (40) begin
      `checkd(c.randomize(), 1);
      `checkd(c.color <= BLACK, 1);
      `checkd(c.color == BLACK, 0);
    end

    // Test 2: randc enum with range constraint - run multiple trials,
    // verify only valid enum members produced and sequence varies
    all_same = 1;
    first_seq = 0;
    for (int trial = 0; trial < 3; trial++) begin
      ac = new;
      this_seq = 0;
      for (int j = 0; j < 4; j++) color_seen[j] = 0;
      repeat (40) begin
        `checkd(ac.randomize(), 1);
        `checkd(ac.color <= WHITE, 1);
        color_seen[ac.color] = 1;
      end
      // Record first 4 values for sequence comparison
      repeat (4) begin
        `checkd(ac.randomize(), 1);
        this_seq = this_seq * 8 + int'(ac.color);
      end
      `checkd(color_seen[0], 1);
      `checkd(color_seen[1], 1);
      `checkd(color_seen[2], 1);
      `checkd(color_seen[3], 1);
      if (trial == 0) first_seq = this_seq;
      else if (this_seq != first_seq) all_same = 0;
    end
    `checkd(all_same, 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
