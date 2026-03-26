// DESCRIPTION: Verilator: covergroup type coverage averages across instances by default
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int value);
    cp: coverpoint value {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  cg cov_a = new;
  cg cov_b = new;

  int covered;
  int total;
  real cov;

  initial begin
    cov_a.sample(0);

    if (cov_a.get_inst_coverage() != 50.0) $stop;
    if (cov_b.get_inst_coverage() != 0.0) $stop;

    cov = cg::get_coverage(covered, total);
    if (covered != 1) $stop;
    if (total != 4) $stop;
    if (cov != 25.0) $stop;
    if (cov_a.get_coverage() != 25.0) $stop;

    cov_b.sample(1);

    if (cov_a.get_inst_coverage() != 50.0) $stop;
    if (cov_b.get_inst_coverage() != 50.0) $stop;

    cov = cg::get_coverage(covered, total);
    if (covered != 2) $stop;
    if (total != 4) $stop;
    if (cov != 50.0) $stop;
    if (cov_b.get_coverage() != 50.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
