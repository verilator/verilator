// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a, int b);
    type_option.weight = 2;
    type_option.goal = 91;
    type_option.comment = "cg_type";
    type_option.strobe = 1;
    type_option.merge_instances = 1;
    type_option.distribute_first = 1;

    option.name = "cg_inst";
    option.weight = 3;
    option.goal = 92;
    option.comment = "cg_opt";
    option.at_least = 4;
    option.auto_bin_max = 5;
    option.cross_num_print_missing = 6;
    option.detect_overlap = 1;
    option.per_instance = 1;
    option.get_inst_coverage = 1;

    cpa: coverpoint a {
      type_option.weight = 7;
      type_option.goal = 93;
      type_option.comment = "cpa_type";

      option.weight = 8;
      option.goal = 94;
      option.comment = "cpa_opt";
      option.at_least = 2;
      option.auto_bin_max = 9;
      option.detect_overlap = 1;

      bins zero = {0};
      bins one = {1};
    }

    cpb: coverpoint b {
      bins zero = {0};
      bins one = {1};
    }

    ab: cross cpa, cpb {
      type_option.weight = 10;
      type_option.goal = 95;
      type_option.comment = "cross_type";

      option.weight = 11;
      option.goal = 96;
      option.comment = "cross_opt";
      option.at_least = 2;
    }
  endgroup

  cg cov = new;

  initial begin
    if (cov.type_option.weight != 2) $stop;
    if (cov.type_option.goal != 91) $stop;
    if (cov.type_option.comment != "cg_type") $stop;
    if (cov.type_option.strobe != 1) $stop;
    if (cov.type_option.merge_instances != 1) $stop;
    if (cov.type_option.distribute_first != 1) $stop;

    if (cov.option.name != "cg_inst") $stop;
    if (cov.option.weight != 3) $stop;
    if (cov.option.goal != 92) $stop;
    if (cov.option.comment != "cg_opt") $stop;
    if (cov.option.at_least != 4) $stop;
    if (cov.option.auto_bin_max != 5) $stop;
    if (cov.option.cross_num_print_missing != 6) $stop;
    if (cov.option.detect_overlap != 1) $stop;
    if (cov.option.per_instance != 1) $stop;
    if (cov.option.get_inst_coverage != 1) $stop;

    if (cov.cpa.type_option.weight != 7) $stop;
    if (cov.cpa.type_option.goal != 93) $stop;
    if (cov.cpa.type_option.comment != "cpa_type") $stop;
    if (cov.cpa.option.weight != 8) $stop;
    if (cov.cpa.option.goal != 94) $stop;
    if (cov.cpa.option.comment != "cpa_opt") $stop;
    if (cov.cpa.option.at_least != 2) $stop;
    if (cov.cpa.option.auto_bin_max != 9) $stop;
    if (cov.cpa.option.detect_overlap != 1) $stop;

    if (cov.ab.type_option.weight != 10) $stop;
    if (cov.ab.type_option.goal != 95) $stop;
    if (cov.ab.type_option.comment != "cross_type") $stop;
    if (cov.ab.option.weight != 11) $stop;
    if (cov.ab.option.goal != 96) $stop;
    if (cov.ab.option.comment != "cross_opt") $stop;
    if (cov.ab.option.at_least != 2) $stop;

    cov.sample(0, 0);
    cov.sample(0, 0);
    if (cov.cpa.get_inst_coverage() != 50.0) $stop;
    if (cov.ab.get_inst_coverage() != 25.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
