// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  class CgCls;
    int m_x;
    int m_z;

    covergroup cov1 @m_z;
      coverpoint m_x {
        bins lo = {[0:1]};
        bins hi = {[2:3]};
      }
    endgroup

    function new();
      cov1 = new;
    endfunction
  endclass

  CgCls c = new;

  initial begin
    c.m_x = 0;
    c.m_z = 1;
    c.cov1.sample(c.m_x);
    c.m_x = 3;
    c.m_z = 2;
    c.cov1.sample(c.m_x);
    $display("coverage = %f", c.cov1.m_x.get_inst_coverage());
    if (c.cov1.m_x.get_inst_coverage() != 100.0) $stop();
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
