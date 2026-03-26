// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  logic [0:0] a;
  logic [0:0] b;
  logic en;

  covergroup cg;
    my_cg_id: cross a, b iff (en);
    ab_bins: cross a, b {
      bins a0_any = binsof(a) intersect {0};
      bins a1_b1 = binsof(a) intersect {1} && binsof(b) intersect {1};
    }
  endgroup

  cg cov = new;

  initial begin
    a = 0;
    b = 0;
    en = 1;
    cov.sample();
    if (cov.my_cg_id.get_inst_coverage() != 25.0) $stop;
    if (cov.ab_bins.get_inst_coverage() != 50.0) $stop;

    a = 1;
    b = 1;
    en = 1;
    cov.sample();
    if (cov.my_cg_id.get_inst_coverage() != 50.0) $stop;
    if (cov.ab_bins.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
