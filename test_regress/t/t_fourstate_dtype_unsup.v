// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  logic x;
  logic y;
} bar;

module t;
  logic q [$];
  logic p [13];
  logic a [integer];
  bar c;
endmodule
