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

module t;
  clk_iface ci ();
  clk_driver drv;

  int x = 0;
  always @(posedge ci.clk) x = x + 1;

  initial begin
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
