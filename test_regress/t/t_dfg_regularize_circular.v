// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module A (
  output [2:0] Y
);
endmodule

module B;
  wire [2:0] w1;
  wire w2;
  A A (
    .Y({ w1[2], w1[0], w2 })
  );
  assign w1[1] = w1[2];
endmodule
