// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  int a;

  covergroup cg @@ (begin funca or end funcb);
    cp: coverpoint a {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  cg cov = new;

  function void funca();
  endfunction

  function void funcb();
    a = 1;
  endfunction

  initial begin
    int covered_bins;
    int total_bins;

    a = 0;
    funca();
    if (cov.cp.get_inst_coverage() != 50.0) $stop;

    funcb();
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 2) $stop;
    if (total_bins != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
