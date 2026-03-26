// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a);
    cp: coverpoint a {
      bins split[3] = {0, 1, [4:5], 9};
      bins each[] = {[10:11], 13};
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(0);
    cov.sample(4);
    cov.sample(9);
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    cov.sample(10);
    cov.sample(11);
    cov.sample(13);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 6) $stop;
    if (total_bins != 6) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
