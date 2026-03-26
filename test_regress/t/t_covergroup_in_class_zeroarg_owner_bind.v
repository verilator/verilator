// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  class CgCls;
    int color;

    covergroup cov1(int a);
      cp_ctor: coverpoint a {
        bins hit = {2};
      }
      cp_color: coverpoint color {
        bins lo = {[0:1]};
        bins hi = {[2:3]};
      }
    endgroup

    function new();
      cov1 = new(2);
    endfunction

    function void sample_now();
      cov1.sample();
    endfunction
  endclass

  CgCls c = new;

  initial begin
    c.color = 0;
    c.sample_now();
    c.color = 3;
    c.cov1.sample();
    $display("ctor coverage = %f", c.cov1.cp_ctor.get_inst_coverage());
    $display("color coverage = %f", c.cov1.cp_color.get_inst_coverage());
    if (c.cov1.cp_ctor.get_inst_coverage() != 100.0) $stop();
    if (c.cov1.cp_color.get_inst_coverage() != 100.0) $stop();
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule