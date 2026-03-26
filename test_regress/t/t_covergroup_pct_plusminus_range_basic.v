// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a);
    cp: coverpoint a {
      bins near_ten = {[10 +%- 20]};
      bins near_five = {[5 +%- 20.0]};
    }
  endgroup

  cg cov = new;

  initial begin
    cov.sample(7);
    if (cov.cp.get_inst_coverage() != 0.0) $stop;

    cov.sample(8);
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    cov.sample(6);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    cov.sample(12);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
