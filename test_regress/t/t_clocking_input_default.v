// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ms / 1ns
module t;
  bit clk = 0;
  bit data = 1;
  bit cb_data;

  initial forever #5 clk = ~clk;
  assign cb_data = cb.data;
  clocking cb @(posedge clk);
    input data;
  endclocking

  initial begin
    @(posedge clk) data = 0;
  end

  initial begin
    #4 if (data != 1) $stop;
    if (cb.data != 0) $stop;
    #1;
    #1step;
    if (cb.data != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
