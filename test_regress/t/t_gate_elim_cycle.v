// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module GND(output G);
  assign G = 0;
endmodule

module CARRY2(
  output [1:0] CO,
  input        CI,
  input  [1:0] DI, S
);
  assign CO[0] = S[0] ? CI    : DI[0];
  assign CO[1] = S[1] ? CO[0] : DI[1];
endmodule

module A;
  wire const0;
  wire ci;
  GND GND (
    .G(const0)
  );
  CARRY2 CARRY2 (
    .CO(),

    .CI(ci),
    .DI({const0,const0}),
    .S({const0,const0})
  );
endmodule
