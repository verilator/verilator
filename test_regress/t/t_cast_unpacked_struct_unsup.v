// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  class Cls;
    byte hi;
    byte lo;
  endclass

  typedef struct {
    byte hi;
    byte lo;
  } s16_t;

  typedef struct {string s;} str_t;

  typedef struct {byte w[*];} wild_t;

  typedef union {
    int i;
    int j;
  } uni_t;

  s16_t s16;
  str_t sts;
  wild_t wild;
  Cls obj;
  byte dyn[];
  byte que[$];
  string str;
  int word;
  uni_t uni;

  initial begin
    s16 = s16_t'({<<8{dyn}});  // Stream of a dynamically sized array
    s16 = s16_t'({<<8{que}});  // Or queue
    s16 = s16_t'({<<8{dyn, s16}});  // Also concatenated with other values
    word = int'({<<8{dyn, s16}});  // Also cast to an integral type
    word = int'({<<8{{>>{dyn}}}});  // Also in another stream
    word = int'({>>{uni, s16}});  // Stream of a union
    s16 = s16_t'({>>{uni}});  // Also alone, which the stream reports
    s16 = s16_t'(str);  // Dynamically sized string
    sts = str_t'(s16);  // Dynamically sized string member
    s16 = s16_t'(wild);  // Dynamically sized associative array member
    s16 = s16_t'(obj);  // Class handle
  end

endmodule
