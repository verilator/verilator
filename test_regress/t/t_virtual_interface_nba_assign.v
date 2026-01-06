// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface clk_if;
  bit a;
  bit clk;
endinterface

interface inf;
  bit clk;
  bit v;

  clocking cb @(posedge clk);
    inout v;
  endclocking
endinterface

class Clocker;
  virtual clk_if clk;

  task clock();
    fork forever #1 clk.clk = ~clk.clk;
    join_none
  endtask
endclass

module t;
  clk_if c();
  inf i();
  assign i.clk = c.clk;
  Clocker clocker;
  initial begin
    i.clk = 0;
    i.v = 0;
    clocker = new;
    clocker.clk = c;
    clocker.clock();
    i.cb.v <= 1;
    #5;
    $stop;
  end
  initial @(posedge i.cb.v) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
