// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ms / 1ns
module t;
  event e;
  bit data = 0;

  clocking cb @e;
    input #0 data;
  endclocking

  initial begin
    #1;
    data = 1;
    -> e;
    #1;
    if (cb.data !== 1'b1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
