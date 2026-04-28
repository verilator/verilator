// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test ignore_bins - excluded from coverage

module t (/*AUTOARG*/);
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  logic [3:0] data;
  logic [1:0] data2;  // 2-bit signal for range-boundary tests

  covergroup cg;
    coverpoint data {
      bins low      = {[0:3]};
      bins high     = {[8:11]};
      ignore_bins reserved  = {[12:15]};
      ignore_bins catch_all = default;  // default ignore-bin: all values not in other bins are ignored
      ignore_bins arr[]     = {4, 5};   // array form: one ignore-bin per value
      wildcard ignore_bins wib = {4'b1?00};  // wildcard ignore-bin with don't-care bits
      illegal_bins bad[] = {6, 7};   // illegal array form: one illegal-bin per value
    }
  endgroup

  // cg2: ignore_bins using a range - auto-bins are created only for values not in the range.
  // Also tests range-boundary conditions: when lo==0 or hi==maxVal, the range check simplifies.
  // Also tests ignore_bins with a transition list.
  covergroup cg2;
    cp_auto: coverpoint data2 {
      ignore_bins ign = {[2:3]};  // range ignore, no regular bins -> auto-bins created
      ignore_bins ign_trans = (0 => 1);  // ignore the 0->1 transition
    }
    cp_bounds: coverpoint data2 {
      bins lo  = {[0:1]};  // lower range (lo=0, no lower-bound check needed)
      bins hi  = {[2:3]};  // upper range (hi=maxVal for 2-bit, no upper-bound check needed)
    }
    cp_full: coverpoint data2 {
      bins all = {[0:3]};  // full range (lo=0 and hi=maxVal: matches all values)
    }
  endgroup

  cg  cg_inst;
  cg2 cg2_inst;

  initial begin
    cg_inst  = new;
    cg2_inst = new;

    data = 13; cg_inst.sample();   // reserved - ignored
    `checkr(cg_inst.get_inst_coverage(), 0.0);
    data = 1;  cg_inst.sample();   // low
    `checkr(cg_inst.get_inst_coverage(), 50.0);
    data = 10; cg_inst.sample();   // high
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    data2 = 0; cg2_inst.sample();  // auto_0, lo, all
    data2 = 1; cg2_inst.sample();  // auto_1, lo, all
    data2 = 2; cg2_inst.sample();  // ign, hi, all
    `checkr(cg2_inst.get_inst_coverage(), 100.0);
    data2 = 3; cg2_inst.sample();  // ign, hi, all
    `checkr(cg2_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
