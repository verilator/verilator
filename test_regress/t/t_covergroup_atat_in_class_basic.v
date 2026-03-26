// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  class worker;
    int a;

    covergroup cg @@ (begin funca or end funcb);
      cp: coverpoint a {
        bins zero = {0};
        bins one = {1};
      }
    endgroup

    function new();
      cg = new;
    endfunction

    function void funca();
    endfunction

    function void funcb();
      a = 1;
    endfunction
  endclass

  worker w = new;

  initial begin
    int covered_bins;
    int total_bins;

    w.a = 0;
    w.funca();
    if (w.cg.cp.get_inst_coverage() != 50.0) $stop;

    w.funcb();
    if (w.cg.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (w.cg.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 2) $stop;
    if (total_bins != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
