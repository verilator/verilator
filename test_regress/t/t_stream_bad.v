// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module t;

  logic [31:0] packed_data_32;
  byte byte_in[4];
  logic [3:0] x = 4'($random());

  initial begin
    packed_data_32 = {<<$random{byte_in}};
    packed_data_32 = {<<x{byte_in}};
    packed_data_32 = {<<0{byte_in}};
    packed_data_32 = {<<-1{byte_in}};
    packed_data_32 = {<<33'h1_0000_0000{byte_in}};
    packed_data_32 = {<<4'bx{byte_in}};
  end

  // An inout port connection is not an assignment, so a stream is not valid
  wire [31:0] io_bus;
  sub_inout i_sub_inout (.io({>>{io_bus}}));

  // A ref port connection is a hierarchical reference, not an assignment,
  // so a stream is not valid
  logic [31:0] ref_var;
  sub_ref i_sub_ref (.r({>>{ref_var}}));

  // An associative array or class is illegal in a streaming destination type
  class Cls;
  endclass

  initial begin
    typedef byte assoc_t[int];
    typedef struct {
      byte member[int];
    } assoc_struct_t;
    byte source_q[$];
    byte source_d[];
    assoc_t assoc_dest;
    byte wildcard_dest[*];
    assoc_t dyn_of_assoc_dest[];
    assoc_t queue_of_assoc_dest[$];
    Cls class_dest;
    assoc_struct_t struct_dest;
    assoc_dest = {>>{source_q}};
    assoc_dest = {<<8{source_d}};
    wildcard_dest = {<<8{source_q}};
    wildcard_dest = {>>{source_d}};
    dyn_of_assoc_dest = {>>{source_q}};
    queue_of_assoc_dest = {>>{source_q}};
    class_dest = {>>{source_q}};
    struct_dest = {>>{source_q}};
  end

  // A struct type shared by many members is checked once
  initial begin
    typedef struct {byte q[$];} nest0_t;
    typedef struct {nest0_t a, b, c, d;} nest1_t;
    typedef struct {nest1_t a, b, c, d;} nest2_t;
    typedef struct {nest2_t a, b, c, d;} nest3_t;
    typedef struct {nest3_t a, b, c, d;} nest4_t;
    typedef struct {nest4_t a, b, c, d;} nest5_t;
    typedef struct {nest5_t a, b, c, d;} nest6_t;
    typedef struct {nest6_t a, b, c, d;} nest7_t;
    typedef struct {nest7_t a, b, c, d;} nest8_t;
    typedef struct {nest8_t a, b, c, d;} nest9_t;
    typedef struct {nest9_t a, b, c, d;} nest10_t;
    typedef struct {nest10_t a, b, c, d;} nest11_t;
    typedef struct {nest11_t a, b, c, d;} nest12_t;
    typedef struct {nest12_t a, b, c, d;} nest13_t;
    typedef struct {nest13_t a, b, c, d;} nest14_t;
    typedef struct {nest14_t a, b, c, d;} nest15_t;
    typedef struct {nest15_t a, b, c, d;} nest16_t;
    typedef struct {
      nest16_t nest;
      byte member[int];
    } nest_assoc_t;
    byte source_q[$];
    nest_assoc_t nest_dest;
    nest_dest = {>>{source_q}};
  end

  // A destination that is not a bit-stream type is illegal
  initial begin
    typedef union {
      byte a;
      shortint b;
    } union_t;
    byte source_q[$];
    union_t union_dest;
    real real_dest;
    event event_dest;
    real real_dyn_dest[];
    chandle chandle_dyn_dest[];
    event event_dyn_dest[];
    union_dest = {>>{source_q}};
    real_dest = {>>{source_q}};
    event_dest = {>>{source_q}};
    real_dyn_dest = {>>{source_q}};
    chandle_dyn_dest = {>>{source_q}};
    event_dyn_dest = {>>{source_q}};
  end

endmodule

module sub_inout (
    inout wire [31:0] io
);
endmodule

module sub_ref (
    ref logic [31:0] r
);
endmodule
