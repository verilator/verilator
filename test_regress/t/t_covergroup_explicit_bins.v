// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int value, bit en);
    option.per_instance = 1;

    a_cp: coverpoint value iff (en) {
      bins zero = {0};
      bins low = {[1:2]};
      bins hi = {[3:4]};
    }

    b_cp: coverpoint value {
      bins exact = {5};
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;
    real cov_inst;
    real cov_type;

    cov.sample(0, 1'b1);
    cov.sample(1, 1'b1);
    cov.sample(2, 1'b0);
    cov.sample(3, 1'b1);
    cov.sample(5, 1'b1);

    if (cov.a_cp.get_inst_coverage() != 100.0) $stop;
    if (cov.b_cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    cov_inst = cov.get_inst_coverage(covered_bins, total_bins);
    if (cov_inst != 100.0) $stop;
    if (covered_bins != 4) $stop;
    if (total_bins != 4) $stop;

    covered_bins = 0;
    total_bins = 0;
    cov_type = cov.get_coverage(covered_bins, total_bins);
    if (cov_type != 100.0) $stop;
    if (covered_bins != 4) $stop;
    if (total_bins != 4) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
