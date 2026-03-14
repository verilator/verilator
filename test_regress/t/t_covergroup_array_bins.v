// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test array bins - separate bin per value

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

  initial begin
    cg cg_inst;

    cg_inst = new();

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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
