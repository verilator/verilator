// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unpacked structures as DPI arguments, passed as C structures (IEEE 1800-2023 H.7.8)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  typedef enum bit [2:0] {
    E1 = 1,
    E6 = 6
  } enum_t;
  typedef struct packed {
    bit [3:0] hi;
    logic [2:0] lo;
  } packed_t;
  typedef logic logic_t;
  // A member of each type DPI passes
  typedef struct {
    byte b;
    byte unsigned bu;
    shortint si;
    int i;
    int unsigned iu;
    longint li;
    longint unsigned liu;
    real r;
    chandle ch;
    string s;
    bit bt;
    logic lg;
    bit [6:0] bv7;
    logic [64:0] lv65;
    bit [95:0] bv96;
    integer ig;
    time tm;
    enum_t en;
    packed_t pk;
    bit [1:0][7:0] pa;
    logic_t [6:0] lt;
  } basic_t;
endpackage

module t;
  typedef pkg::basic_t basic_t;
  // Nested structures, and unpacked arrays of any ranges
  typedef struct {
    int x;
    bit [32:0] v[3:1];
    struct {
      byte a;
      shortint m[1:2][0:2];
    } anon;
  } inner_t;
  typedef struct {
    basic_t basic;
    inner_t inner[2];
  } outer_t;

  import "DPI-C" task dpii_basic(
    input basic_t i,
    output basic_t o,
    inout basic_t io
  );
  import "DPI-C" function void dpii_outer(
    input outer_t i,
    output outer_t o,
    inout outer_t io
  );
  import "DPI-C" function void dpii_array(
    input inner_t i[2][1:3],
    output inner_t o[3:1],
    inout inner_t io[0:1]
  );
  import "DPI-C" context function void dpii_check_export(int n);
  import "DPI-C" function int dpii_failure();
  export "DPI-C" function dpix_outer;
  export "DPI-C" function dpix_array;

  // Named as a member of the model class, which declares the exports
  typedef struct {int x;} eval;

  // Values from 'n', as the C side makes them, except chandles which C makes non-null
  function automatic basic_t fillBasic(int n);
    basic_t p;
    p.b = byte'(-1 - n);
    p.bu = byte'(200 + n);
    p.si = shortint'(-1000 - n);
    p.i = -100000 - n;
    p.iu = 32'hf000_0000 + n;
    p.li = -64'sd5_000_000_000 - longint'(n);
    p.liu = 64'hf000_0000_0000_0000 + 64'(n);
    p.r = 1.5 + n;
    p.ch = null;
    p.s = $sformatf("s%0d", n);
    p.bt = n[0];
    p.lg = !n[0];
    p.bv7 = 7'h55 ^ 7'(n);
    p.lv65 = {1'b1, 32'hdead_beef, 32'(n)};
    p.bv96 = {32'h1234_5678, 32'(n), 32'h9abc_def0};
    p.ig = -7 - n;
    p.tm = {32'(n), 32'h89ab_cdef};
    p.en = n[0] ? pkg::E6 : pkg::E1;
    p.pk = '{hi: 4'(n + 3), lo: 3'(n)};
    p.pa = {8'(n), 8'ha5};
    p.lt = 7'(n + 9);
    return p;
  endfunction
  function automatic void checkBasic(basic_t p, int n);
    basic_t e = fillBasic(n);
    `checkh(p.b, e.b);
    `checkh(p.bu, e.bu);
    `checkh(p.si, e.si);
    `checkh(p.i, e.i);
    `checkh(p.iu, e.iu);
    `checkh(p.li, e.li);
    `checkh(p.liu, e.liu);
    `checkr(p.r, e.r);
    if (p.ch == null) `stop;
    `checks(p.s, e.s);
    `checkh(p.bt, e.bt);
    `checkh(p.lg, e.lg);
    `checkh(p.bv7, e.bv7);
    `checkh(p.lv65, e.lv65);
    `checkh(p.bv96, e.bv96);
    `checkh(p.ig, e.ig);
    `checkh(p.tm, e.tm);
    `checkh(p.en, e.en);
    `checkh(p.pk, e.pk);
    `checkh(p.pa, e.pa);
    `checkh(p.lt, e.lt);
  endfunction

  function automatic inner_t fillInner(int n);
    inner_t p;
    p.x = 1000 * n + 7;
    for (int k = 1; k <= 3; ++k) p.v[k] = {1'b1, 32'(16 * n + k)};
    p.anon.a = byte'(n + 100);
    for (int r = 1; r <= 2; ++r) begin
      for (int c = 0; c <= 2; ++c) p.anon.m[r][c] = shortint'(100 * n + 10 * r + c);
    end
    return p;
  endfunction
  function automatic void checkInner(inner_t p, int n);
    inner_t e = fillInner(n);
    `checkh(p.x, e.x);
    for (int k = 1; k <= 3; ++k) `checkh(p.v[k], e.v[k]);
    `checkh(p.anon.a, e.anon.a);
    for (int r = 1; r <= 2; ++r) begin
      for (int c = 0; c <= 2; ++c) `checkh(p.anon.m[r][c], e.anon.m[r][c]);
    end
  endfunction

  function automatic outer_t fillOuter(int n);
    outer_t p;
    p.basic = fillBasic(n);
    for (int k = 0; k < 2; ++k) p.inner[k] = fillInner(n + k);
    return p;
  endfunction
  function automatic void checkOuter(outer_t p, int n);
    checkBasic(p.basic, n);
    for (int k = 0; k < 2; ++k) checkInner(p.inner[k], n + k);
  endfunction

  int n_dpix_outer = 0;
  function void dpix_outer(input outer_t i, output outer_t o, inout outer_t io);
    checkOuter(i, n_dpix_outer);
    checkOuter(io, n_dpix_outer + 1);
    o = fillOuter(n_dpix_outer + 2);
    io = fillOuter(n_dpix_outer + 3);
    n_dpix_outer += 10;
  endfunction

  function void dpix_array(input eval i[2], output eval o[2]);
    foreach (i[k]) o[k].x = i[k].x + 1;
  endfunction

  sub #(.W(1)) u_sub1 ();
  sub #(.W(2)) u_sub2 ();

  initial begin
    for (int n = 0; n < 30; n += 10) begin
      begin
        basic_t o;
        basic_t io;
        io = fillBasic(n + 1);
        dpii_basic(fillBasic(n), o, io);
        checkBasic(o, n + 2);
        checkBasic(io, n + 3);
      end
      begin
        outer_t o;
        outer_t io;
        io = fillOuter(n + 1);
        dpii_outer(fillOuter(n), o, io);
        checkOuter(o, n + 2);
        checkOuter(io, n + 3);
      end
      begin
        inner_t i[2][1:3];
        inner_t o[3:1];
        inner_t io[0:1];
        for (int a = 0; a < 2; ++a) begin
          for (int b = 1; b <= 3; ++b) i[a][b] = fillInner(n + 3 * a + b - 1);
        end
        for (int k = 0; k < 2; ++k) io[k] = fillInner(n + 6 + k);
        dpii_array(i, o, io);
        for (int k = 1; k <= 3; ++k) checkInner(o[k], n + 7 + k);
        for (int k = 0; k < 2; ++k) checkInner(io[k], n + 11 + k);
      end
      dpii_check_export(n);
    end
    `checkd(n_dpix_outer, 30);
    `checkd(u_sub1.f(), 2);
    `checkd(u_sub2.f(), 3);
    `checkd(dpii_failure(), 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

// Specializations passing the same structure
module sub #(
    parameter int W = 0
);
  typedef struct {int w;} sub_t;
  import "DPI-C" function int dpii_sub(input sub_t i);
  function automatic int f();
    sub_t s = '{w: W};
    return dpii_sub(s);
  endfunction
endmodule
