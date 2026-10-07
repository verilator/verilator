// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef union {
    int i;
    byte b;
  } u_t;

  u_t u;

  typedef union packed {
    logic [7:0] a;
    logic [7:0] b;
  } p_t;

  p_t p;

  // Assignment patterns are for structures and arrays only (IEEE 1800-2023 10.9)
  initial begin
    u = '{i: 32'h12345678};
    u = '{default: 5};
    u = '{32'h12345678};
    u = '{int : 7};
    u = u_t'{i: 1};
    p = '{a: 8'h12};
    p = '{default: 8'h34};
    p = '{8'h56};
  end

  // Nested in a pattern of an array, queue or structure of unions
  typedef struct {
    u_t m;
    int x;
  } s_t;

  initial begin
    u_t ua[2];
    u_t uq[$];
    s_t s;
    ua = '{'{i: 1}, '{i: 2}};
    uq = '{'{i: 3}};
    s = '{m: '{i: 4}, x: 5};
  end

endmodule
