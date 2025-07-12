// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t();

  enum bit signed [3:0] {OK1 = -1} ok1_t;  // As is signed, loss of 1 bits is ok per IEEE
  enum bit signed [3:0] {OK2 = 3} ok2_t;

  typedef enum [2:0] { VALUE_BAD1 = 8 } enum_t;

  enum bit [4:0] {BAD2[4] = 100} bad2;

  enum logic [3:0] {BAD3 = 5'bxxxxx} bad3;

  initial $stop;
endmodule
