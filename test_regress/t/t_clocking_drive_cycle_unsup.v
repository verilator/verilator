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

  ev_if vbus ();
  virtual ev_if vvif;
  initial begin
    vvif = vbus;
    vvif.ecb.e <= ##1 1;
  end
endmodule

interface ev_if;
  event ev;
  bit e;
  clocking ecb @(ev);
    output e;
  endclocking
endinterface
