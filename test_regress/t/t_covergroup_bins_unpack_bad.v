// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int index;
  function automatic int existing_function();
    return 1;
  endfunction
  int bad_with = existing_function with (1);
  typedef int associative_t[int];
  associative_t associative_values;
  int wildcard_values[*];
  string string_values[$];
  int nested_values[2][3];
  chandle handle_values[$];
  typedef enum {ONE = 1, TWO = 2} enum_t;
  enum_t enum_value;
  int integer_values[$];
  class value_t;
  endclass
  typedef value_t class_array_t[$];
  class_array_t class_values;

  covergroup cg with function sample (bit value);
    cp: coverpoint value {
      bins brace_lhs[] = {4'd1, 4'd2} == 8'h12;
      bins root_increment[] = ++index;
      bins brace_lhs_single[] = {4'd1} == 4'h1;
      bins brace_lhs_triple[] = {4'd1, 4'd2, 4'd3} == 12'h123;
      bins associative[] = associative_values;
      bins wildcard_associative[] = wildcard_values;
      bins strings[] = string_values;
      bins nested[] = nested_values;
      bins handles[] = handle_values;
      bins classes[] = class_values;
    }
  endgroup

  covergroup cg_enum;
    cp: coverpoint enum_value {
      bins integers[] = integer_values;
    }
  endgroup
  cg_enum enum_inst = new;

  cg cg_inst = new;
endmodule
