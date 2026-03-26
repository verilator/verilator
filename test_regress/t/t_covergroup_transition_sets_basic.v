// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a);
    cp: coverpoint a {
      bins values     = (0, 2);
      bins step_sets  = (1, 3 => 4, 6);
      wildcard bins wvalues = (4'b1??1, 4'b01??);
      wildcard bins wstep   = (4'b00?? => 4'b11??);
    }
  endgroup

  cg cov = new;

  initial begin
    cov.sample(0);
    if (cov.cp.get_inst_coverage() != 25.0) $stop;

    cov.sample(9);
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    cov.sample(1);
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    cov.sample(4);
    if (cov.cp.get_inst_coverage() != 75.0) $stop;

    cov.sample(2);
    if (cov.cp.get_inst_coverage() != 75.0) $stop;

    cov.sample(12);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
