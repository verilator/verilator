// DESCRIPTION: Verilator: Verilog Test module for issue #3817
// addDriver() was causing use-after-free and segfaulting during Verilation
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Jevin Sweval.
// SPDX-License-Identifier: CC0-1.0

module t (
  output [2:0] c_b_a,
  input a,
  input b,
  input c
);
  assign c_b_a = {c, {b, a}};
endmodule
