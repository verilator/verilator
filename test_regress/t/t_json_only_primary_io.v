// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module top (
    clk,
    a1,
    a2,
    ready
);
  input clk;
  input a1;
  input a2;
  output ready;

  wire ready_reg;

  and2_x1 and_cell (
      .a1(a1),
      .a2(a2),
      .zn(ready_reg)
  );

  assign ready = ready_reg;
endmodule

module and2_x1 (
    input wire a1,
    input wire a2,
    output wire zn
);
  assign zn = (a1 & a2);
endmodule
