// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef struct {
    struct {logic [7:0] value;} arr[2];
    logic [7:0] mem[2];
    logic [7:0] m2[2][2];
    logic flag;
  } st_t;
  typedef struct {logic [7:0] x[2];} a_t;
  typedef struct {logic [7:0] y[2];} b_t;
  typedef union {
    a_t a;
    b_t b;
  } u_t;
  typedef struct {
    u_t u;
    a_t e[2];
    logic flag;
  } su_t;
  st_t s;
  su_t su;
  int i;
  int j;
  logic [7:0] q;
  logic [7:0] q2;
  logic [7:0] qu;
  logic [7:0] qe;
  assign q = s.arr[i].value;
  // One error
  assign q2 = s.m2[i][j];
  // Overlaid by su.u.a.x
  assign qu = su.u.b.y[i];
  // Below su.e[1]
  assign qe = su.e[1].x[i];

  // Through a read-write reference
  logic [7:0] qr;
  function automatic logic [7:0] get(ref logic [7:0] value);
    return value;
  endfunction

  initial begin
    force s.arr[1].value = 8'ha5;
    force s.m2[1][0] = 8'h30;
    force su.u.a.x[1] = 8'h31;
    force su.e[1] = su.e[0];
    qr = get(s.arr[i].value);
    $finish;
  end
endmodule
