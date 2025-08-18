// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  int a;
  always @* a = 100;
  initial begin
    #1;
    if (a != 0) $stop;
  end
endmodule
