// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Monitor;
  bit value;
  static bit clk;

  covergroup unclocked;
    cp: coverpoint value;
  endgroup

  covergroup reconstructed;
    cp: coverpoint value;
  endgroup

  covergroup constant_point;
    cp: coverpoint 1'b1;
  endgroup

  covergroup static_clocked @(posedge clk);
    cp: coverpoint value;
  endgroup

  function new();
    reconstructed = new;
  endfunction

  function void build();
    unclocked = new;
    reconstructed = new;
    constant_point = new;
    static_clocked = new;
  endfunction

  function void clear();
    reconstructed = null;
  endfunction
endclass

class OtherConstructor;
  function new(Monitor mon);
    mon.unclocked = new;
  endfunction
endclass

module t;
  Monitor mon;
  OtherConstructor other;

  initial begin
    mon = new;
    mon.build();
    mon.clear();
    other = new(mon);
    mon.unclocked = new;
    $finish;
  end
endmodule
