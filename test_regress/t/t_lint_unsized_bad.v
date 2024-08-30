// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   bit [256:0] num = 'd123456789123456789123456789;
   bit [256:0] num = 'h123456789123456789123456789;
   bit [256:0] num = 'o123456789123456789123456789;
   bit [256:0] num = 'b10101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010;
endmodule
