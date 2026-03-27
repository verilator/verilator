// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test ignore_bins - excluded from coverage

module t (/*AUTOARG*/);
  logic [3:0] data;
  logic [1:0] data2;  // 2-bit signal for range-boundary tests

  covergroup cg;
    coverpoint data {
      bins low      = {[0:3]};
      bins high     = {[8:11]};
      ignore_bins reserved  = {[12:15]};
      ignore_bins catch_all = default;  // null rangesp: exercises generateBinMatchCode !fullCondp
      wildcard ignore_bins wib = {4'b1?00};  // wildcard ignore bins (L7084-7085)
    }
  endgroup

  // Exercises:
  //   extractValuesFromRange AstInsideRange branch (ignore_bins range, no regular bins)
  //   createImplicitAutoBins with excluded range values
  //   makeRangeCondition: skipUpperCheck=true (hi=maxVal) and both-skip (BitTrue)
  //   ignore_bins with transition list (L7102-7104)
  covergroup cg2;
    cp_auto: coverpoint data2 {
      ignore_bins ign = {[2:3]};  // range ignore, no regular bins -> auto-bins created
      ignore_bins ign_trans = (0 => 1);  // ignore_bins with transition (L7102-7104)
    }
    cp_bounds: coverpoint data2 {
      bins lo  = {[0:1]};  // lo=0: skipLowerCheck -> AstLte
      bins hi  = {[2:3]};  // hi=maxVal (2-bit): skipUpperCheck -> AstGte
    }
    cp_full: coverpoint data2 {
      bins all = {[0:3]};  // lo=0 and hi=maxVal: both skip -> AstConst(BitTrue)
    }
  endgroup

  cg  cg_inst;
  cg2 cg2_inst;

  initial begin
    cg_inst  = new;
    cg2_inst = new;

    data = 13; cg_inst.sample();   // reserved - ignored
    data = 1;  cg_inst.sample();   // low
    data = 10; cg_inst.sample();   // high

    data2 = 0; cg2_inst.sample();  // auto_0, lo, all
    data2 = 1; cg2_inst.sample();  // auto_1, lo, all
    data2 = 2; cg2_inst.sample();  // ign, hi, all
    data2 = 3; cg2_inst.sample();  // ign, hi, all

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
