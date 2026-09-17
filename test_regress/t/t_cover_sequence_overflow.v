// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk;
  int cyc;

  always #1 clk = !clk;
  always @(posedge clk) cyc <= cyc + 1;

  sequence eight_lengths; 1'b1 [* 1: 8]; endsequence
  sequence overflowing;
    eight_lengths ##0 eight_lengths ##0 eight_lengths ##0 eight_lengths ##0 eight_lengths
        ##0 eight_lengths ##0 eight_lengths ##0 eight_lengths ##0 eight_lengths ##0 eight_lengths
        ##0 eight_lengths ##0 eight_lengths ##0 eight_lengths;
  endsequence

  // The central coefficient is 26,184,550,496, exceeding UINT32_MAX.
  cover sequence (@(posedge clk) disable iff (cyc == -1) (cyc == 0) ##0 overflowing ##1 1'b0);

  initial begin
    repeat (80) @(posedge clk);
    $finish;
  end
endmodule
