// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface mem_if (
    input wire clk
);
  logic reset;

  clocking cb @(posedge clk);
    output reset;
  endclocking

  modport mp(input clk);

endinterface

module sub (
    mem_if.mp x
);

  initial begin
    x.cb.reset <= 1;
  end

endmodule

module t ();
  logic clk = 0;

  mem_if m_if (clk);
  sub i_sub (m_if);
endmodule
