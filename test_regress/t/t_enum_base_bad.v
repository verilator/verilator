// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef struct {int a;} s_t;

  typedef enum s_t {  // BAD
    EN_ZERO
  } bad_t;

  typedef int int_t;
  enum int_t [1:0] {  // BAD enum type
    INTRANGE_VAL
  } intrange_e;

  typedef bit [1:0][1:0] d2_t;
  enum d2_t {  // BAD enum type
    TD2_VAL
  } td2_e;

  enum logic [1:0][1:0] {  // BAD enum type
    D2_VAL
  } d2_e;

  typedef struct packed {int x;} str_t;
  enum str_t {  // BAD enum type
    STR_VAL
  } str_e;

  typedef enum {ENUM_VAL} enum_t;
  enum enum_t {  // BAD enum type
    ENUMT_VAL
  } enumt_val;

  typedef logic array2_t[1:0];
  enum array2_t {  // BAD enum type
    ARRAY2_VAL
  } array2_e;

  initial $stop;

endmodule
