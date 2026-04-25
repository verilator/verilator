// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test array bins - separate bin per value, including InsideRange and AstRange

module t;
  bit [7:0] data;

  covergroup cg;
    coverpoint data {
      // Array bins: creates 3 separate bins
      bins values[] = {1, 5, 9};

      // Non-array bin: creates 1 bin covering all values
      bins grouped = {2, 6, 10};
    }
  endgroup

  // cg2: exercises InsideRange in array bins (e.g., bins r[] = {[0:3]})
  covergroup cg2;
    cp: coverpoint data {
      bins range_arr[] = {[0:3]};   // InsideRange -> 4 separate bins
    }
  endgroup

  // cg3: exercises AstRange in array bins (e.g., bins r[N] = {[lo:hi]})
  covergroup cg3;
    cp: coverpoint data {
      bins range_sized[4] = {[4:7]};  // AstRange with explicit count
    }
  endgroup

  initial begin
    cg  cg_inst;
    cg2 cg2_inst;
    cg3 cg3_inst;

    cg_inst  = new();
    cg2_inst = new();
    cg3_inst = new();

    // Hit first array bin value (1)
    data = 1;
    cg_inst.sample();

    // Hit second array bin value (5)
    data = 5;
    cg_inst.sample();

    // Hit the grouped bin (covers all of 2, 6, 10)
    data = 6;
    cg_inst.sample();

    // Hit third array bin value (9)
    data = 9;
    cg_inst.sample();

    // Verify hitting other values in grouped bin doesn't increase coverage
    data = 2;
    cg_inst.sample();

    // Hit range_arr bins (InsideRange [0:3])
    data = 0; cg2_inst.sample();
    data = 1; cg2_inst.sample();
    data = 2; cg2_inst.sample();

    // Hit range_sized bins (AstRange [4:7])
    data = 4; cg3_inst.sample();
    data = 5; cg3_inst.sample();
    data = 6; cg3_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
