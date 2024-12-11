// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t(input [255:0] clk);
   // Do not exclude from inlining wide reference assignments.
   mod1 mod1(clk);
   mod2 mod2(clk);
endmodule

module mod1(input [255:0] clk);
endmodule

module mod2(input [255:0] clk);
endmodule
