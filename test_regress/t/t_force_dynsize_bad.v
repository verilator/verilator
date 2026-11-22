// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Force and release are a form of procedural continuous assignment (IEEE 1800-2023 10.6.2), so
// shall not write elements of dynamically sized variables, or parts of them, non-static class
// properties, nor automatic variables (IEEE 1800-2023 6.21)

typedef logic [6:0] row_t[3:2];

typedef struct {
  logic [6:0] q[$];
  logic [6:0] d[];
  logic [6:0] a[int];
  logic [6:0] w[*];
  row_t ar[int];
  row_t qr[$];
  row_t f;
} dyn_t;

class Cls;
  logic [6:0] p;
  row_t pa;
endclass

interface Ifc;
  row_t w[*];
endinterface

module t;
  // Elements of dynamically sized variables
  logic [6:0] q[$];
  logic [6:0] d[];
  logic [6:0] a[int];
  logic [6:0] w[*];
  row_t qr[$];
  row_t f;
  initial begin
    force f[2] = 7'h55;  // OK
    force q[1] = 7'h55;  // Error
    force d[1] = 7'h55;  // Error
    force a[3] = 7'h55;  // Error
    force w[3] = 7'h55;  // Error
    force q[1][5:3] = 3'h5;  // Error
    force q[$] = 7'h55;  // Error
    force q[$-1] = 7'h55;  // Error
    force qr[$][2] = 7'h55;  // Error
    release f[2];  // OK
    release q[1];  // Error
    release q[$];  // Error
  end

  // Also of struct members
  dyn_t s;
  initial begin
    force s.f[2] = 7'h55;  // OK
    force s.q[1] = 7'h55;  // Error
    force s.d[1] = 7'h55;  // Error
    force s.a[3] = 7'h55;  // Error
    force s.w[3] = 7'h55;  // Error
    force s.ar[3][2] = 7'h55;  // Error
    force s.qr[$][2] = 7'h55;  // Error
    release s.a[3];  // Error
  end

  // Also of interface members
  Ifc ifc ();
  initial force ifc.w[3][2] = 7'h55;  // Error

  // Non-static class properties, also in a conditional statement
  Cls c;
  row_t f2;
  bit en;
  initial begin
    force c.p = 7'h55;  // Error
    force c.pa[2] = 7'h55;  // Error
    if (en) force c.pa = f2;  // Error
    release c.p;  // Error
  end

  // Automatic variables
  initial begin
    automatic logic [6:0] av;
    force av = 7'h55;  // Error
  end
endmodule
