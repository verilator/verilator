// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [7:0] i,
    output logic [31:0] o[2]
);
  logic [31:0] r0;
  logic [31:0] r1;
  logic [31:0] r2;
  logic [31:0] r3;
  logic [31:0] r4;
  logic [31:0] r5;
  logic [31:0] r6;
  logic [31:0] r7;
  logic [31:0] r8;
  logic [31:0] r9;
  logic [31:0] r10;
  logic [31:0] r11;
  logic [31:0] r12;
  logic [31:0] r13;
  logic [31:0] r14;
  logic [31:0] r15;
  always_ff @(posedge clk) r0 <= (r0 + {24'd0, i}) ^ 32'h00000001;
  always_ff @(posedge clk) r1 <= (r1 + r0) ^ 32'h00000002;
  always_ff @(posedge clk) r2 <= (r2 + r1) ^ 32'h00000003;
  always_ff @(posedge clk) r3 <= (r3 + r2) ^ 32'h00000004;
  always_ff @(posedge clk) r4 <= (r4 + r3) ^ 32'h00000005;
  always_ff @(posedge clk) r5 <= (r5 + r4) ^ 32'h00000006;
  always_ff @(posedge clk) r6 <= (r6 + r5) ^ 32'h00000007;
  always_ff @(posedge clk) r7 <= (r7 + r6) ^ 32'h00000008;
  always_ff @(posedge clk) r8 <= (r8 + {24'd0, i}) ^ 32'h00000009;
  always_ff @(posedge clk) r9 <= (r9 + r8) ^ 32'h0000000a;
  always_ff @(posedge clk) r10 <= (r10 + r9) ^ 32'h0000000b;
  always_ff @(posedge clk) r11 <= (r11 + r10) ^ 32'h0000000c;
  always_ff @(posedge clk) r12 <= (r12 + r11) ^ 32'h0000000d;
  always_ff @(posedge clk) r13 <= (r13 + r12) ^ 32'h0000000e;
  always_ff @(posedge clk) r14 <= (r14 + r13) ^ 32'h0000000f;
  always_ff @(posedge clk) r15 <= (r15 + r14) ^ 32'h00000010;
  assign o[0] = r0 ^ r3 ^ r6;
  assign o[1] = r8 ^ r11 ^ r14;
endmodule
