// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a, int b);
    cpa: coverpoint a {
      bins lo = {[0:1]};
      bins hi = {[2:3]};
    }
    cpb: coverpoint b {
      bins zero = {0};
      bins one = {1};
    }
    ab: cross cpa, cpb {
      bins lo_any = binsof(cpa) intersect {[0:1]};
      bins hi_b1  = binsof(cpa.hi) intersect {3} && binsof(cpb.one);
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(0, 0);
    if (cov.ab.get_inst_coverage() != 50.0) $stop;

    cov.sample(1, 1);
    if (cov.ab.get_inst_coverage() != 50.0) $stop;

    cov.sample(2, 0);
    if (cov.ab.get_inst_coverage() != 50.0) $stop;

    cov.sample(3, 1);
    if (cov.ab.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 6) $stop;
    if (total_bins != 6) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
