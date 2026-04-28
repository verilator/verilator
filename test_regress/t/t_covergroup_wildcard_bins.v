// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test wildcard bins with don't care matching

module t;
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  bit [7:0] data;

  covergroup cg;
    coverpoint data {
      // Match any value with upper nibble = 4'b0000
      wildcard bins low = {8'b0000_????};

      // Match any value with upper nibble = 4'b1111
      wildcard bins high = {8'b1111_????};

      // Match specific pattern with don't cares
      wildcard bins pattern = {8'b10?0_11??};

      // Non-wildcard range bin: [min:max] with min != max
      bins mid_range = {[8'h40 : 8'h4F]};

      // Wildcard bin using single-value range [5:5] (min==max, equivalent to a single value)
      wildcard bins wc_point = {[8'd5 : 8'd5]};
    }
  endgroup

  initial begin
    cg cg_inst;

    cg_inst = new();

    // Test low bin (upper nibble = 0000)
    // Note: 8'b0000_0101 = 5 = 8'd5, so it matches BOTH 'low' and 'wc_point'
    data = 8'b0000_0101;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 40.0);  // 2/5: low + wc_point hit simultaneously

    // Test high bin (upper nibble = 1111)
    data = 8'b1111_1010;  // Should match 'high'
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 60.0);  // 3/5

    // Test pattern bin (10?0_11??)
    data = 8'b1000_1101;  // Should match 'pattern' (10[0]0_11[0]1)
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 80.0);  // 4/5

    // Verify another pattern match
    data = 8'b1010_1111;  // Should also match 'pattern' (10[1]0_11[1]1)
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 80.0);  // 4/5 — same bin, no increase

    // Test mid_range bin: [0x40:0x4F]
    data = 8'h45;  // Should match 'mid_range'
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0); // 5/5: all bins now hit

    // wc_point (value 5) was already hit in the first sample; confirm no regression
    data = 8'd5;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // Verify non-matching value doesn't change coverage
    data = 8'b0101_0101;  // Shouldn't match any bin
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
