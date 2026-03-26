// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a, int b);
    option.per_instance = 1;

    cpa: coverpoint a {
      bins zero = {0};
      bins one = {1};
    }

    cpb: coverpoint b {
      bins zero = {0};
      bins one = {1};
    }

    ab: cross cpa, cpb;
  endgroup

  cg cov = new;

  initial begin
    cov.sample(0, 0);
    cov.sample(0, 1);
    cov.sample(1, 0);
    cov.sample(1, 1);

    if (cov.cpa.get_inst_coverage() != 100.0) $stop;
    if (cov.cpb.get_inst_coverage() != 100.0) $stop;
    if (cov.ab.get_inst_coverage() != 100.0) $stop;
    if (cov.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
