// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  class CgCls;
    int m_x;
    bit m_en;

    covergroup cov1;
      cp: coverpoint (m_x + 1) iff (m_en) {
        bins two = {2};
        bins three = {3};
      }
    endgroup

    function new();
      cov1 = new;
    endfunction
  endclass

  CgCls c = new;

  initial begin
    int covered_bins;
    int total_bins;

    c.m_en = 0;
    c.m_x = 1;
    c.cov1.sample();
    if (c.cov1.cp.get_inst_coverage() != 0.0) $stop;

    c.m_en = 1;
    c.m_x = 1;
    c.cov1.sample();
    if (c.cov1.cp.get_inst_coverage() != 50.0) $stop;

    c.m_x = 2;
    c.cov1.sample();
    if (c.cov1.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (c.cov1.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 2) $stop;
    if (total_bins != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule