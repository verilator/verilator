// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a);
    cp: coverpoint a {
      bins near_five = {[5 +/- 2]};
      bins near_ten  = {[10 +/- 1]};
    }
  endgroup

  cg cov = new;

  initial begin
    cov.sample(2);
    if (cov.cp.get_inst_coverage() != 0.0) $stop;

    cov.sample(3);
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    cov.sample(11);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
