// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(bit [2:0] a);
    cp: coverpoint a {
      bins even[] = a with (item % 2 == 0);
      bins low_pair[2] = a with (item < 4);
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(3'd0);
    if (cov.cp.get_inst_coverage() != (200.0 / 6.0)) $stop;

    cov.sample(3'd2);
    if (cov.cp.get_inst_coverage() != (400.0 / 6.0)) $stop;

    cov.sample(3'd4);
    if (cov.cp.get_inst_coverage() != (500.0 / 6.0)) $stop;

    cov.sample(3'd6);
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
