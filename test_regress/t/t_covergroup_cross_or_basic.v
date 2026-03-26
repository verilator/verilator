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
      bins either_a0_or_b1 = binsof(cpa.zero) || binsof(cpb.one);
      bins rhs_with_only   = binsof(cpa.one) || binsof(cpb.one) with (a == 0);
      bins paren_with      = (binsof(cpa.one) || binsof(cpb.one)) with (a == 0);
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(1, 0);
    if (cov.ab.get_inst_coverage() != (100.0 / 3.0)) $stop;

    cov.sample(0, 0);
    if (cov.ab.get_inst_coverage() != (200.0 / 3.0)) $stop;

    cov.sample(0, 1);
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
