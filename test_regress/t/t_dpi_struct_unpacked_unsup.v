// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package a;
  typedef struct {int x;} same_t;
endpackage

package b;
  typedef struct {byte x;} same_t;
endpackage

module sub #(
    parameter type T = struct {int a;}
);
  import "DPI-C" function void dpii_param(input T s);
  initial begin
    T v;
    dpii_param(v);
  end
endmodule

module t;
  typedef struct {int x;} \escaped-t ;
  typedef struct {int template;} keyword_t;
  typedef union {
    int i;
    byte b;
  } union_t;

  // Structure types without typedef names usable in C
  import "DPI-C" function void dpii_anon(input struct {int a;} s);
  import "DPI-C" function void dpii_escaped(input \escaped-t s);
  // Member names not usable in C
  import "DPI-C" function void dpii_keyword(input keyword_t s);
  // Different structures of the same name
  import "DPI-C" function void dpii_same_a(input a::same_t s);
  import "DPI-C" function void dpii_same_b(input b::same_t s);

  export "DPI-C" function dpix_union;
  function void dpix_union(input union_t u);
  endfunction

  sub u_sub ();

  initial begin
    \escaped-t e;
    keyword_t k;
    a::same_t sa;
    b::same_t sb;
    dpii_anon('{a: 1});
    dpii_escaped(e);
    dpii_keyword(k);
    dpii_same_a(sa);
    dpii_same_b(sb);
  end
endmodule
