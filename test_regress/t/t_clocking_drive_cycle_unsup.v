// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub;
  bit s;
  clocking scb @(posedge t.clk);
    output s;
  endclocking
  initial scb.s <= ##1 1;
endmodule

module t;
  bit clk;
  sub sub ();
  initial sub.scb.s <= ##1 1;
endmodule
