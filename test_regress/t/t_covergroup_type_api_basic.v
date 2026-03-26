// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;
  int covered, total;
  real cov;

  covergroup cg with function sample(int a, int b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a { bins zero = {0}; bins one = {1}; }
    cp_b: coverpoint b { bins zero = {0}; bins one = {1}; }
    cr_ab: cross cp_a, cp_b;
  endgroup

  cg cov_a = new;
  cg cov_b = new;

  initial begin
    cov_a.sample(0, 0);
    if (cov_a.cp_a.get_inst_coverage() != 50.0) $stop;
    if (cov_b.cp_a.get_inst_coverage() != 0.0) $stop;
    if (cov_a.cp_a.get_type_coverage() != 50.0) $stop;
    if (cov_a.cp_b.get_type_coverage() != 50.0) $stop;
    if (cov_a.cr_ab.get_type_coverage() != 25.0) $stop;
    if (cov_a.cp_a.get_type_coverage() != cov_a.cp_a.get_coverage()) $stop;
    if (cov_a.cr_ab.get_type_coverage() != cov_a.cr_ab.get_coverage()) $stop;

    cov = cov_a.get_type_coverage(covered, total);
    if (cov != 37.5) $stop;
    if (covered != 3) $stop;
    if (total != 8) $stop;
    if (cov != cov_a.get_coverage()) $stop;
    if (cov != cg::get_type_coverage(covered, total)) $stop;

    cov_b.sample(1, 1);
    if (cov_a.cp_a.get_type_coverage() != 100.0) $stop;
    if (cov_b.cp_b.get_coverage() != 100.0) $stop;
    if (cov_a.cr_ab.get_type_coverage() != 50.0) $stop;
    cov = cov_b.get_type_coverage(covered, total);
    if (cov != 75.0) $stop;
    if (covered != 6) $stop;
    if (total != 8) $stop;
    if (cov != cg::get_type_coverage()) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
