// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  typedef struct {
    byte bytes[$];
  } queue_struct_t;

  typedef struct {
    byte bytes[];
  } dynamic_struct_t;

  typedef struct {
    byte bytes[int];
  } associative_struct_t;

  typedef union {
    byte a;
    logic [15:0] b;
  } unpacked_union_t;

  typedef struct {
    unpacked_union_t u;
  } union_struct_t;

  typedef struct {
    string s;
  } string_struct_t;

  typedef struct {
    chandle c;
  } chandle_struct_t;

  typedef struct {
    event e;
  } event_struct_t;

  logic [255:0] out;
  queue_struct_t queue_struct;
  dynamic_struct_t dynamic_struct;
  associative_struct_t associative_struct;
  union_struct_t union_struct;
  string_struct_t string_struct;
  chandle_struct_t chandle_struct;
  event_struct_t event_struct;

  initial begin
    out = {>>{queue_struct}};
    out = {>>{dynamic_struct}};
    out = {>>{associative_struct}};
    out = {>>{union_struct}};
    out = {>>{string_struct}};
    out = {>>{chandle_struct}};
    out = {>>{event_struct}};
  end

endmodule
