// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef struct {
  logic a;
  logic b;
} unpacked_struct_t;

typedef union {
  logic a;
  logic b;
} unpacked_union_t;

module t;
  unpacked_struct_t [0:0][0:0] unpacked_struct_array;
  unpacked_union_t [0:0][0:0] unpacked_union_array;

  typedef struct {logic a;} [0:0][0:0] direct_unpacked_struct_array_t;
endmodule
