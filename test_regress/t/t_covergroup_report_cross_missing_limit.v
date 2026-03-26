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
      option.cross_num_print_missing = 2;
    }
  endgroup

  cg cov = new;

  initial begin
    cov.sample(0, 0);
    if (cov.ab.get_inst_coverage() != 25.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
