// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a, bit en);
    cp: coverpoint a {
      bins even = {[0:7]} with (item % 2 == 0);
      bins odd_small = a with (item == 1 || item == 3);
      bins gated = {4, 5, 6, 7} with (en);
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(0, 0);
    if (cov.cp.get_inst_coverage() != (100.0 / 3.0)) $stop;

    cov.sample(3, 0);
    if (cov.cp.get_inst_coverage() != (200.0 / 3.0)) $stop;

    cov.sample(4, 1);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 3) $stop;
    if (total_bins != 3) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
