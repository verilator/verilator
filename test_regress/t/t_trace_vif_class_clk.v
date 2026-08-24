// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns / 1ns
`define STRINGIFY(x) `"x`"

interface clk_iface;
  bit clk;
endinterface

// Interface containing a sub-interface, only accessed through the containing interface
interface sub_iface;
  bit clk;
endinterface

interface top_iface;
  sub_iface sub ();
endinterface

class clk_driver;
  virtual clk_iface vif;
  function new(virtual clk_iface vif);
    this.vif = vif;
  endfunction

  task run();
    vif.clk = 1'b0;
    forever #5 vif.clk = ~vif.clk;
  endtask
endclass

// Writes a sub-interface member through a chained virtual interface select
class sub_toggler;
  virtual top_iface vif;
  function new(virtual top_iface vif);
    this.vif = vif;
  endfunction

  function void toggle();
    vif.sub.clk = ~vif.sub.clk;
  endfunction
endclass

module t;
  clk_iface ci ();
  clk_driver drv;
  top_iface ti ();
  sub_toggler tog;

  int x = 0;
  always @(posedge ci.clk) x = x + 1;
  always @(negedge ci.clk) tog.toggle();

  initial begin
    tog = new(ti);
    drv = new(ci);
    drv.run();
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(0, t);
    repeat (5) @(posedge ci.clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
