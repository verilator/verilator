// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog
//
// Assignment compatibility test.
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  int a;
  int b;
} struct_t;

module t;

  logic unpackedA[2];
  logic unpackedB[3];
  logic unpackedC[3][2];
  logic unpackedD[4][2];
  struct_t unpackedE[4][2];
  logic nonAggregate;
  logic queueA[$];

  assign unpackedB = unpackedA;
  assign unpackedB = unpackedC;
  assign unpackedD = unpackedC;
  assign unpackedE = unpackedD;
  assign nonAggregate = unpackedA;
endmodule
