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

  typedef byte byte_t;
  typedef shortint shortint_t;
  typedef int int_t;
  typedef longint longint_t;
  typedef integer integer_t;
  typedef time time_t;
  typedef int_t int2_t;
  byte_t [1:0] byte_array;
  shortint_t [1:0] shortint_array;
  int_t [1:0] int_array;
  longint_t [1:0] longint_array;
  integer_t [1:0] integer_array;
  time_t [1:0] time_array;
  int2_t [1:0][2:0] int2_array;

  typedef bit [2:0] bit3_t;
  typedef enum int {A, B} enum_t;
  bit3_t [1:0] ok_bit_array;
  enum_t [1:0] ok_enum_array;
endmodule
