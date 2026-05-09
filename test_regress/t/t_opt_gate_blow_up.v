// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module top(
  input wire [31:0] a
);

  wire [31:0] w00, w01, w02, w03, w04, w05, w06, w07, w08, w09;
  wire [31:0] w10, w11, w12, w13, w14, w15, w16, w17, w18, w19;

  // V3Gate used to inline all the continuous assignments into
  // the always_comb block, resultingin an exponential increase
  // in AST size.

  always_comb begin
    $display(w19);
  end

  assign w19 = w18 + (w18 >> 1);
  assign w18 = w17 + (w17 >> 1);
  assign w17 = w16 + (w16 >> 1);
  assign w16 = w15 + (w15 >> 1);
  assign w15 = w14 + (w14 >> 1);
  assign w14 = w13 + (w13 >> 1);
  assign w13 = w12 + (w12 >> 1);
  assign w12 = w11 + (w11 >> 1);
  assign w11 = w10 + (w10 >> 1);
  assign w10 = w09 + (w09 >> 1);
  assign w09 = w08 + (w08 >> 1);
  assign w08 = w07 + (w07 >> 1);
  assign w07 = w06 + (w06 >> 1);
  assign w06 = w05 + (w05 >> 1);
  assign w05 = w04 + (w04 >> 1);
  assign w04 = w03 + (w03 >> 1);
  assign w03 = w02 + (w02 >> 1);
  assign w02 = w01 + (w01 >> 1);
  assign w01 = w00 + (w00 >> 1);
  assign w00 = a + (a >> 1);

endmodule
