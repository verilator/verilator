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
    logic [6:0] lo;
  } s15_t;

  typedef union {
    logic [14:0] a;
    bit [14:0] b;
  } u15_t;

  typedef struct {
    real r;
    logic [6:0] t;
  } real_t;

  typedef struct {chandle h;} ch_t;

  typedef byte assoc_t[int];

  typedef struct {byte a[int];} sa_t;

  typedef struct {Cls c[2];} sc_t;

  typedef byte bytes_t[4];

  initial begin
    s15_t s;
    u15_t u;
    real_t rs;
    ch_t ch;
    int i;
    logic [14:0] v15;
    logic [70:0] v71;
    Cls obj;
    assoc_t aa;
    sa_t sa;
    sc_t sc;
    bytes_t b4;
    s = s15_t'(i);  // Bad: 32 bits to 15
    i = int'(s);  // Bad: 15 bits to 32
    b4 = bytes_t'(s);  // Bad: 15 bits to 32
    i = int'(s15_t'{8'h12, 7'h34});  // Bad: 15 bits to 32, from a pattern
    i = int'(s15_t'(15'h1234));  // Bad: 15 bits to 32, from a cast
    s = s15_t'({<<i{v15}});  // Bad: a slice size that is not a constant
    s = s15_t'({<<-1{v15}});  // Bad: a negative slice size
    u = u15_t'(s);  // Bad: an unpacked union is not a bit-stream type
    s = s15_t'(u);  // Bad: an unpacked union is not a bit-stream type
    rs = real_t'(v71);  // Bad: a real is not a bit-stream type
    ch = ch_t'(64'h0);  // Bad: a chandle is not a bit-stream type
    obj = Cls'(s);  // Bad: a class destination
    aa = assoc_t'(s);  // Bad: an associative array destination
    sa = sa_t'(s);  // Bad: an associative array in the destination
    sc = sc_t'(s);  // Bad: a class in the destination
    i = int'(b4[2:5]);  // Bad: a slice out of range, as the operand
    b4 = bytes_t'({i[15:8], i[7:0]});  // Bad: braces of too few elements
    begin
      typedef byte b2_t[2];
      b2_t b2;
      b2 = b2_t'({2{i[7:0]}});  // Bad: replication in an unpacked array concatenation
    end
  end

endmodule
