// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Paul Swirhun.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/);

  // Different width types that should fail casting
  typedef logic [7:0] byte_array_t[];
  typedef logic [7:0] byte_queue_t[$];
  typedef logic [15:0] word_array_t[];
  typedef logic [15:0] word_queue_t[$];

  // Struct types with same width but different structure
  typedef struct packed {logic [3:0] a, b;} struct8_t;
  typedef struct8_t struct_array_t[];
  typedef struct8_t struct_queue_t[$];

  // Non-byte types for string casting restrictions
  typedef int int_array_t[];
  typedef int int_queue_t[$];

  // Narrow bit widths that use CData but aren't byte-compatible
  typedef logic [0:0] bit1_array_t[];
  typedef logic [0:0] bit1_queue_t[$];
  typedef logic [2:0] bit3_array_t[];
  typedef logic [2:0] bit3_queue_t[$];
  typedef logic [6:0] bit7_array_t[];
  typedef logic [6:0] bit7_queue_t[$];

  initial begin
    byte_array_t   byte_arr;
    byte_queue_t   byte_que;
    word_array_t   word_arr;
    word_queue_t   word_que;
    struct_array_t struct_arr;
    struct_queue_t struct_que;
    int_array_t    int_arr;
    int_queue_t    int_que;
    bit1_array_t   bit1_arr;
    bit1_queue_t   bit1_que;
    bit3_array_t   bit3_arr;
    bit3_queue_t   bit3_que;
    bit7_array_t   bit7_arr;
    bit7_queue_t   bit7_que;
    string         str;

    // These should all fail compilation due to width mismatch

    // Different width: byte vs word
    byte_arr = byte_array_t'(word_que);
    word_que = word_queue_t'(byte_arr);

    // Different structure: struct vs logic (same width)
    byte_arr = byte_array_t'(struct_que);
    struct_arr = struct_array_t'(byte_que);

    // String casting to non-byte types should fail
    str = string'(int_arr);
    str = string'(int_que);
    str = string'(word_arr);
    str = string'(word_que);

    // String casting to narrow bit widths should fail
    str = string'(bit1_arr);
    str = string'(bit1_que);
    str = string'(bit3_arr);
    str = string'(bit3_que);
    str = string'(bit7_arr);
    str = string'(bit7_que);

    // String casting from non-byte types should fail
    int_arr = int_array_t'(str);
    int_que = int_queue_t'(str);
    word_arr = word_array_t'(str);
    word_que = word_queue_t'(str);

    // String casting from narrow bit widths should fail
    bit1_arr = bit1_array_t'(str);
    bit1_que = bit1_queue_t'(str);
    bit3_arr = bit3_array_t'(str);
    bit3_que = bit3_queue_t'(str);
    bit7_arr = bit7_array_t'(str);
    bit7_que = bit7_queue_t'(str);

    $write("*-* Should not reach here *-*\n");
    $finish;
  end

endmodule
