// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;
  int covered, total;
  real cov;

  covergroup cg_inst with function sample(int a, int b);
    cpa: coverpoint a {
      option.weight = 1;
      bins zero = {0};
      bins one = {1};
    }
    cpb: coverpoint b {
      option.weight = 3;
      bins zero = {0};
      bins one = {1};
      bins two = {2};
      bins three = {3};
    }
  endgroup

  covergroup cg_type with function sample(int a, int b);
    type_option.merge_instances = 1;
    cpa: coverpoint a {
      type_option.weight = 1;
      bins zero = {0};
      bins one = {1};
    }
    cpb: coverpoint b {
      type_option.weight = 3;
      bins zero = {0};
      bins one = {1};
      bins two = {2};
      bins three = {3};
    }
  endgroup

  cg_inst cov_inst = new;
  cg_type cov_a = new;
  cg_type cov_b = new;

  initial begin
    cov_inst.sample(0, 0);
    cov = cov_inst.get_inst_coverage(covered, total);
    if (covered != 4) $stop;
    if (total != 14) $stop;
    if (cov != (400.0 / 14.0)) $stop;

    cov_inst.sample(1, 3);
    cov = cov_inst.get_inst_coverage(covered, total);
    if (covered != 8) $stop;
    if (total != 14) $stop;
    if (cov != (800.0 / 14.0)) $stop;

    cov_a.sample(0, 0);
    cov = cg_type::get_coverage(covered, total);
    if (covered != 4) $stop;
    if (total != 14) $stop;
    if (cov != (400.0 / 14.0)) $stop;

    cov_b.sample(1, 3);
    cov = cov_a.get_type_coverage(covered, total);
    if (covered != 8) $stop;
    if (total != 14) $stop;
    if (cov != (800.0 / 14.0)) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
