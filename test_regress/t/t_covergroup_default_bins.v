// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test default bins - catch-all for values not in other bins

module t;
  bit [7:0] data;

  covergroup cg;
    coverpoint data {
      bins low = {[0:3]};
      bins high = {[12:15]};
      bins other = default;  // Catches everything else (4-11, 16+)
    }
  endgroup

  // Covergroup with default as the ONLY bin: exercises defaultCondp=BitTrue path
  covergroup cg2;
    cp_only_default: coverpoint data {
      bins all = default;
    }
  endgroup

  initial begin
    cg  cg_inst;
    cg2 cg2_inst;

    cg_inst  = new();
    cg2_inst = new();

    // Hit low bin
    data = 2;
    cg_inst.sample();
    cg2_inst.sample();

    // Hit high bin
    data = 14;
    cg_inst.sample();
    cg2_inst.sample();

    // Hit default bin with value 7 (not in low or high)
    data = 7;
    cg_inst.sample();
    cg2_inst.sample();

    // Hit another default value (should not increase coverage)
    data = 20;
    cg_inst.sample();
    cg2_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
