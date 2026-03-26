// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a);
    cp: coverpoint a {
      bins rise = (0 => 1);
      bins other = default sequence;
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(0);
    if (cov.cp.get_inst_coverage() != 0.0) $stop;

    cov.sample(1);
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    cov.sample(3);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 2) $stop;
    if (total_bins != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
