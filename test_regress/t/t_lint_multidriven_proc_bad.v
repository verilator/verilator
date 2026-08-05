// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aisha Salimgereyeva
// SPDX-License-Identifier: CC0-1.0

// Same clock: two plain always blocks drive the whole of 'q', reported by
// MULTIDRIVENPROC.
module t (
    input wire clk,
    input wire d,
    output logic q
);

  always @(posedge clk) q <= d;
  always @(posedge clk) q <= ~d;

endmodule

// Different clocks: reported by MULTIDRIVEN (on by default). MULTIDRIVENPROC is
// suppressed here so the conflict is reported only once.
module t2 (
    input wire clka,
    input wire clkb,
    input wire d,
    output logic q
);

  always @(posedge clka) q <= d;
  always @(posedge clkb) q <= ~d;

endmodule
