// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test ignore_bins - excluded from coverage

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [3:0] data;
  logic [1:0] data2;  // 2-bit signal for range-boundary tests

  covergroup cg;
    coverpoint data {
      bins low = {[0 : 3]};
      bins high = {[8 : 11]};
      ignore_bins reserved = {[12 : 15]};
      ignore_bins catch_all = default;  // default ignore-bin: all values not in other bins are ignored
      ignore_bins arr[] = {4, 5};  // array form: one ignore-bin per value
      wildcard ignore_bins wib = {4'b1?00};  // wildcard ignore-bin with don't-care bits
      illegal_bins bad[] = {6, 7};  // illegal array form: one illegal-bin per value
    }
  endgroup

  // cg2: ignore_bins using a range - auto-bins are created only for values not in the range.
  // Also tests range-boundary conditions: when lo==0 or hi==maxVal, the range check simplifies.
  // Also tests ignore_bins with a transition list.
  covergroup cg2;
    cp_auto: coverpoint data2 {
      ignore_bins ign = {[2 : 3]};  // range ignore, no regular bins -> auto-bins created
      ignore_bins ign_trans = (0 => 1);  // ignore the 0->1 transition
    }
    cp_auto_ub: coverpoint data2 {
      ignore_bins ub = {[2 : $]};  // open-ended ignore: '$' == domain max (3) -> auto-bins for 0,1
    }
    cp_bounds: coverpoint data2 {
      bins lo = {[0 : 1]};  // lower range (lo=0, no lower-bound check needed)
      bins hi = {[2 : 3]};  // upper range (hi=maxVal for 2-bit, no upper-bound check needed)
    }
    cp_full: coverpoint data2 {
      bins all = {[0 : 3]};  // full range (lo=0 and hi=maxVal: matches all values)
    }
  endgroup

  // cg3: open-ended LOWER bound ignore - '$' == domain min (0) -> auto-bins for 2,3
  covergroup cg3;
    cp_auto_lb: coverpoint data2 {
      ignore_bins lb = {[$ : 1]};  // ignore 0,1 -> auto-bins created for 2,3
    }
  endgroup

  cg cg_inst;
  cg2 cg2_inst;
  cg3 cg3_inst;

  initial begin
    cg_inst = new;
    cg2_inst = new;
    cg3_inst = new;

    data = 13;
    cg_inst.sample();  // reserved - ignored
    `checkr(cg_inst.get_inst_coverage(), 0.0);
    data = 1;
    cg_inst.sample();  // low
    `checkr(cg_inst.get_inst_coverage(), 50.0);
    data = 10;
    cg_inst.sample();  // high
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    data2 = 0;
    cg2_inst.sample();  // auto_0, lo, all
    data2 = 1;
    cg2_inst.sample();  // auto_1, lo, all
    data2 = 2;
    cg2_inst.sample();  // ign, hi, all
    `checkr(cg2_inst.get_inst_coverage(), 100.0);
    data2 = 3;
    cg2_inst.sample();  // ign, hi, all
    `checkr(cg2_inst.get_inst_coverage(), 100.0);

    data2 = 0;
    cg3_inst.sample();  // lb (ignored)
    data2 = 2;
    cg3_inst.sample();  // auto_0
    `checkr(cg3_inst.get_inst_coverage(), 50.0);
    data2 = 3;
    cg3_inst.sample();  // auto_1
    `checkr(cg3_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
