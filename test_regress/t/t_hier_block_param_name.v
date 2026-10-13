// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Specializations of a parameterized class are distinct types, but for matching ones, and
// $typename returns their names (IEEE 1800-2023 8.25, 20.6.1).  Hierarchical block 'hb' and the
// parent are Verilated in runs of their own, which each name the specializations they elaborate:
// a specialization has one name in both, and distinct ones distinct names.  hb elaborates two
// specializations of each class, and passes their names to the parent, which elaborates the
// second of those.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A type name as characters, the first the most significant, for a port to pass
localparam int NAME_CHARS = 64;

function automatic logic [8*NAME_CHARS-1:0] to_bits(string name);
  to_bits = '0;
  for (int i = 0; i < name.len() && i < NAME_CHARS; ++i) to_bits[8*(NAME_CHARS-1-i)+:8] = name[i];
endfunction

function automatic string to_name(logic [8*NAME_CHARS-1:0] name_bits);
  to_name = "";
  for (int i = 0; i < NAME_CHARS; ++i) begin
    if (name_bits[8*(NAME_CHARS-1-i)+:8] == 0) break;
    to_name = {to_name, string'(name_bits[8*(NAME_CHARS-1-i)+:8])};
  end
endfunction

// Of a type parameter
class TypeParam #(
    type T = int
);
  T v;
endclass

// Of a parameter not of 32 bits
class ByteParam #(
    bit [7:0] B = 8'd1
);
  bit [7:0] v = B;
endclass

// Of parameters whose values make a long name
class LongParameters #(
    int FIRST_PARAMETER = 1,
    int SECOND_PARAMETER = 2
);
  int v = FIRST_PARAMETER + SECOND_PARAMETER;
endclass

module hb (
    output logic [8*NAME_CHARS-1:0] type_a_name,
    output logic [8*NAME_CHARS-1:0] type_b_name,
    output logic [8*NAME_CHARS-1:0] byte_a_name,
    output logic [8*NAME_CHARS-1:0] byte_b_name,
    output logic [8*NAME_CHARS-1:0] long_a_name,
    output logic [8*NAME_CHARS-1:0] long_b_name
);
  /*verilator hier_block*/
  TypeParam #(byte) type_a;
  TypeParam #(shortint) type_b;
  ByteParam #(8'd2) byte_a;
  ByteParam #(8'd3) byte_b;
  LongParameters #(1111111, 2222222) long_a;
  LongParameters #(3333333, 4444444) long_b;

  // In a procedure, as the handles are dynamic (IEEE 1800-2023 6.21)
  initial begin
    type_a_name = to_bits($typename(type_a));
    type_b_name = to_bits($typename(type_b));
    byte_a_name = to_bits($typename(byte_a));
    byte_b_name = to_bits($typename(byte_b));
    long_a_name = to_bits($typename(long_a));
    long_b_name = to_bits($typename(long_b));
  end
endmodule

module t;
  logic [8*NAME_CHARS-1:0] type_a_name;
  logic [8*NAME_CHARS-1:0] type_b_name;
  logic [8*NAME_CHARS-1:0] byte_a_name;
  logic [8*NAME_CHARS-1:0] byte_b_name;
  logic [8*NAME_CHARS-1:0] long_a_name;
  logic [8*NAME_CHARS-1:0] long_b_name;
  TypeParam #(shortint) type_b;
  ByteParam #(8'd3) byte_b;
  LongParameters #(3333333, 4444444) long_b;

  hb h (.*);

  // Without $finish, which could come before hb's names: the simulation ends, and runs the final
  // blocks, once time zero has run
  final begin
    // A specialization of both has one name in both
    `checks(to_name(type_b_name), $typename(type_b));
    `checks(to_name(byte_b_name), $typename(byte_b));
    `checks(to_name(long_b_name), $typename(long_b));
    // Distinct specializations have distinct names
    `checkd(to_name(type_a_name) != $typename(type_b), 1);
    `checkd(to_name(byte_a_name) != $typename(byte_b), 1);
    `checkd(to_name(long_a_name) != $typename(long_b), 1);
    $write("*-* All Finished *-*\n");
  end
endmodule
