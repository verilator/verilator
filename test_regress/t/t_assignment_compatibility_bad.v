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

typedef struct {
  int a;
  int b;
} ustruct_t;

typedef union {
  int a;
  int b;
} uunion_t;

module t;

  logic unpackedA[2];
  logic unpackedB[3];
  logic unpackedC[3][2];
  logic unpackedD[4][2];
  struct_t unpackedE[4][2];
  logic nonAggregate;
  logic assocArrayA[string];
  logic queueA[$];
  bit queueB[$];
  logic unpackedF[3] = unpackedA;
  bit unpackedG[2] = unpackedB[0:1];

  assign unpackedB = unpackedA;
  assign unpackedB = unpackedC;
  assign unpackedD = unpackedC;
  assign unpackedE = unpackedD;
  assign nonAggregate = unpackedA;
  assign unpackedA = assocArrayA;
  assign queueA = queueB;

  ustruct_t ustructA = 7;
  ustruct_t ustructB[2] = '{7, 8};
  ustruct_t ustructC;
  ustruct_t ustructD[2][2] = '{default: '{7, 8}};
  assign ustructC = '0;
  ustruct_t ustructE = '0;  // Issue #7460
  uunion_t uunionA = 7;

  typedef logic row3_t[3];
  typedef logic row2_t[2];
  row3_t rows3[2];
  row2_t rows2[2];
  assign rows3 = rows2;

  typedef bit [8191:0] wide_t;
  typedef string string_t;
  string_t text_value = "hello";
  string_t text_array[2];
  string_t text_assoc[int];
  string_t text_wild[*];
  string_t text_dyn[];
  string_t text_queue[$];
  wide_t wide_value;
  bit [6:0] narrow_value;
  int integer_value;

  function int bad_return();
    return text_value;
  endfunction

  task take_integer(input int value);
  endtask

  initial begin
    wide_value = text_value;
    narrow_value = text_value;
    integer_value = text_value;
    take_integer(text_value);
    // No string conversion error on top of the earlier error
    integer_value = text_array;
    integer_value = text_array.bad_method;
    integer_value = text_assoc.bad_method;
    integer_value = text_wild.bad_method;
    integer_value = text_dyn.bad_method;
    integer_value = text_queue.bad_method;
  end
endmodule
