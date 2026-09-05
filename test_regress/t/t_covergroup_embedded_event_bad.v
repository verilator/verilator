// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Level;
  bit event_signal;
endclass

class Middle;
  Level level;
endclass

class Monitor;
  bit clk;
  bit [3:0] value;
  Middle middle;

  covergroup cg @(posedge clk or posedge middle.level.event_signal);
    cp: coverpoint value;
  endgroup

  function new();
    middle = new;
    middle.level = new;
  endfunction

  function void build();
    cg = new;
  endfunction
endclass

module t;
  Monitor mon;

  initial begin
    mon = new;
    mon.build();
  end
endmodule
