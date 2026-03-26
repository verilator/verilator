// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(bit a, bit b, bit en);
    int cpa_typed: coverpoint a iff (en) {
      bins zero = {0};
      bins one  = {1};
    }
    var bit cpb_typed: coverpoint b iff (en) {
      bins zero = {0};
      bins one  = {1};
    }
    ab: cross a, b iff (en);
    ab_sel: cross a, b {
      bins a0_any = binsof(a) intersect {0};
      bins a1_b1  = binsof(a) intersect {1} && binsof(b) intersect {1};
    }
  endgroup

  cg cov = new;

  initial begin
    cov.sample(0, 0, 0);
    if (cov.cpa_typed.get_inst_coverage() != 0.0) $stop;
    if (cov.cpb_typed.get_inst_coverage() != 0.0) $stop;

    cov.sample(0, 0, 1);
    if (cov.cpa_typed.get_inst_coverage() != 50.0) $stop;
    if (cov.cpb_typed.get_inst_coverage() != 50.0) $stop;

    cov.sample(0, 1, 1);
    if (cov.cpa_typed.get_inst_coverage() != 50.0) $stop;
    if (cov.cpb_typed.get_inst_coverage() != 100.0) $stop;

    cov.sample(1, 0, 1);
    if (cov.cpa_typed.get_inst_coverage() != 100.0) $stop;
    if (cov.cpb_typed.get_inst_coverage() != 100.0) $stop;

    cov.sample(1, 1, 1);
    if (cov.cpa_typed.get_inst_coverage() != 100.0) $stop;
    if (cov.cpb_typed.get_inst_coverage() != 100.0) $stop;

    if (cov.cpa_typed.get_inst_coverage() != 100.0) $stop;
    if (cov.cpb_typed.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
