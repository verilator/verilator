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
      option.weight = 12;
      option.goal = 77;
      option.comment = "cross";
      option.at_least = 2;
      option.cross_num_print_missing = 9;
    }
  endgroup

  cg cov = new;

  initial begin
    if (cov.ab.option.weight != 12) $stop;
    if (cov.ab.option.goal != 77) $stop;
    if (cov.ab.option.at_least != 2) $stop;
    if (cov.ab.option.comment != "cross") $stop;
    if (cov.ab.option.cross_num_print_missing != 9) $stop;

    cov.sample(0, 0);
    if (cov.ab.get_inst_coverage() != 0.0) $stop;

    cov.sample(0, 0);
    if (cov.ab.get_inst_coverage() != 25.0) $stop;

    cov.sample(0, 1);
    cov.sample(0, 1);
    cov.sample(1, 0);
    cov.sample(1, 0);
    cov.sample(1, 1);
    cov.sample(1, 1);
    if (cov.ab.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
