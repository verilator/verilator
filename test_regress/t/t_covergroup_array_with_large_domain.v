// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(bit [10:0] a);
    cp: coverpoint a {
      option.auto_bin_max = 4;
      bins even[] = a with (item % 2 == 0);
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(11'd0);
    if (cov.cp.get_inst_coverage() != 25.0) $stop;

    cov.sample(11'd512);
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    cov.sample(11'd1024);
    if (cov.cp.get_inst_coverage() != 75.0) $stop;

    cov.sample(11'd1536);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 4) $stop;
    if (total_bins != 4) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
