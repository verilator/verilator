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
  clk_iface ci0 ();
  clk_iface ci1 ();
  clk_driver drv0;
  clk_driver drv1;

  int x0 = 0;
  int x1 = 0;
  always @(posedge ci0.clk) x0 = x0 + 1;
  always @(posedge ci1.clk) x1 = x1 + 1;

  initial begin
    drv0 = new(ci0);
    drv1 = new(ci1);
    fork
      drv0.run();
      drv1.run();
    join_none
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(0, t);
    repeat (5) @(posedge ci0.clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
