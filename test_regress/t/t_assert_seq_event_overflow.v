// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk;

  always #1 clk = !clk;

  sequence never_matches;
    @(posedge clk) 1'b1 [* 1: 1024] ##0 1'b1 [* 1: 1024] ##0 1'b1 [* 1: 1024] ##0
        1'b1 [* 1: 1024] ##1 1'b0;
  endsequence

  always @never_matches $fatal;

  initial begin
    repeat (600) @(posedge clk);
    $finish;
  end
endmodule
