// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a, int b);
    cpa: coverpoint a {
      bins zero = {0};
      bins one = {1};
    }
    cpb: coverpoint b {
      bins zero = {0};
      bins one = {1};
    }
    ab: cross cpa, cpb {
      bins only_a0 = binsof(cpa) with (a == 0);
      bins any_b1  = with (b == 1);
      bins pair11  = binsof(cpa.one) && binsof(cpb.one) with (a == 1 && b == 1);
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(0, 0);
    if (cov.ab.get_inst_coverage() != (100.0 / 3.0)) $stop;

    cov.sample(0, 1);
    if (cov.ab.get_inst_coverage() != (200.0 / 3.0)) $stop;

    cov.sample(1, 0);
    if (cov.ab.get_inst_coverage() != (200.0 / 3.0)) $stop;

    cov.sample(1, 1);
    if (cov.ab.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 7) $stop;
    if (total_bins != 7) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
