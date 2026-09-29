// DESCRIPTION: Verilator: Verilog Test module
//
// An unpacked array parameter whose size comes from another parameter of the
// same instantiation.  The size must come from the overridden parameter, not
// from the module's own default.  See issue #5890.
//
// Checks are all in t's single initial block, ahead of the $finish, as an
// initial block inside an instance may be ordered after it.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Oyvind Janbu
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module m #(
    parameter int N = 1,
    parameter int V[N] = '{0}
) ();
endmodule

// Element width also parameter dependent
module p #(
    parameter int W = 1,
    parameter logic [W-1:0] B[2] = '{0, 0}
) ();
endmodule

// Concatenation value for a parameter with a parameter-dependent width
module c #(
    parameter int W = 1,
    parameter logic [W-1:0] P = '0
) ();
endmodule

// Both dimensions parameter dependent
module d2 #(
    parameter int N = 1,
    parameter int M = 1,
    parameter int V[N][M] = '{'{0}}
) ();
endmodule

// Interfaces are deparameterized separately from cells
interface iface #(
    parameter int N = 1,
    parameter int V[N] = '{0}
) ();
endinterface

// Size from a type parameter
module r #(
    parameter type T = byte,
    parameter T V[$bits(T)] = '{default: 0}
) ();
endmodule

// Whole parameter type is a type parameter
typedef struct packed {
  int a;
  int b;
} wide_t;
typedef struct packed {
  byte a;
  byte b;
} narrow_t;

module s #(
    parameter type T = wide_t,
    parameter T V = '{default: 0}
) ();
endmodule

// Untyped parameter with a parameter-dependent default value (issue #5890)
module u #(
    parameter LEN = 4,
    parameter LST[LEN] = '{LEN{0}}
) ();
endmodule

// Size defaults to zero, so the module's own default is not a legal size
module z #(
    parameter int N = 0,
    parameter int V[N] = '{}
) ();
endmodule

// Target of a bind whose pattern values come from the target's own parameter
module bt #(
    parameter int P = 0
) ();
endmodule
bind bt z #(.N(2), .V('{P, 99})) i_bz ();

// Size from an element of another array parameter
module e #(
    parameter int B[2] = '{1, 1},
    parameter int V[B[0]] = '{0}
) ();
endmodule

// Size from the size of another array parameter
module sz #(
    parameter int B[3] = '{0, 0, 0},
    parameter int V[$size(B)] = '{default: 0}
) ();
endmodule

// Class parameters, reached through a class-scoped reference
class cls #(
    parameter int N = 0,
    parameter int V[N] = '{}
);
  static function int last();
    return V[N-1];
  endfunction
endclass

// Size from a localparam of the parameter port list
module lp #(
    parameter int N = 0,
    localparam int M = N + 1,
    parameter int V[M] = '{default: 0}
) ();
endmodule

// Sizes from values converted to the parameters' declared types
module cv #(
    // verilator lint_off WIDTHTRUNC
    parameter byte N = 1,  // Overridden with a wider value
    // verilator lint_on WIDTHTRUNC
    parameter int B[$bits(N)] = '{default: 0},  // Size from the declared width
    parameter int T[N] = '{default: 0},  // Size from the truncated value
    parameter byte S = 1,
    parameter int G[S < 0 ? 2 : 1] = '{default: 0}  // Size from the signed value
) ();
endmodule

// Scalar width from an element of an array parameter
module sc #(
    parameter int B[1] = '{1},
    parameter logic [B[0]-1:0] P = '0
) ();
endmodule

// Types from typedefs of the module that use its parameters, so non-ANSI
module td;
  parameter int N = 1;
  typedef logic [N-1:0] elem_t;
  typedef struct packed {
    elem_t a;
    logic [3:0] b;
  } pair_t;
  parameter elem_t V[2] = '{default: 0};
  parameter pair_t P[2] = '{default: 0};
  parameter pair_t S = '0;
  pair_t x;
endmodule

// Size overridden from the enclosing module's own parameter
module mid #(
    parameter int M = 1,
    parameter int W[M] = '{0}
) ();
  m #(.N(M), .V(W)) i_pass ();  // Pass the array down
  m #(.N(M + 1), .V('{1, 2, 3, 4})) i_expr ();  // Size from an expression, M == 3
endmodule

module t;
  localparam int TWO = 2;
  typedef int arr3_t[3];
  typedef cls#(.N(3), .V('{4, 5, 6})) cls3_t;

  m #(.N(2), .V('{1, 2})) i_m2 ();
  m #(.N(3), .V('{1, 2, 3})) i_m3 ();
  m #(.N(TWO + 1), .V('{1, 2, 3})) i_m3e ();  // Non-folded size override
  m #(.V('{1})) i_m1 ();  // Size left at its default
  m #(.N(4), .V('{default: 1})) i_m4d ();  // Default in the pattern
  m #(.N(3), .V('{3{1}})) i_m3r ();  // Replication in the pattern
  m #(.N(3), .V(arr3_t'{4, 5, 6})) i_m3t ();  // Pattern with its own type

  p #(.W(8), .B('{8'ha, 8'hb})) i_p ();

  d2 #(.N(2), .M(3), .V('{'{1, 2, 3}, '{4, 5, 6}})) i_d2 ();

  iface #(.N(3), .V('{1, 2, 3})) i_iface ();

  c #(.W(16), .P({8'ha, 8'hb})) i_c ();

  r #(.T(shortint), .V('{16{1}})) i_r ();

  s #(.T(narrow_t), .V('{a: 8'h1, b: 8'h2})) i_sn ();
  s #(.V('{a: 32'h3, b: 32'h4})) i_sw ();  // Type left at its default

  u #(.LEN(8), .LST('{8{0}})) i_u ();
  u #(.LEN(8)) i_ud ();  // Default value must resize with LEN

  mid #(.M(3), .W('{1, 2, 3})) i_mid ();

  z #(.N(1), .V('{9})) i_z1 ();
  z #(.N(3), .V('{5, 6, 7})) i_z3 ();
  bt #(.P(4)) i_bt ();

  e #(.B('{2, 3}), .V('{5, 6})) i_eb ();  // Array parameter given first
  e #(.V('{5, 6}), .B('{2, 3})) i_ea ();  // Array parameter given last
  e #(.V('{5})) i_ed ();  // Array parameter left at its default
  sz #(.B('{1, 2, 3}), .V('{7, 8, 9})) i_sz ();

  lp #(.N(2), .V('{1, 2, 3})) i_lp ();
  lp #(.N(3)) i_lpd ();  // Default value must resize with M

  cv #(.N(257), .B('{8{1}}), .T('{2}), .S(8'hff), .G('{3, 4})) i_cv ();

  sc #(.B('{8}), .P(8'h01)) i_sc1 ();
  sc #(.B('{8}), .P(8'h81)) i_sc81 ();  // Differs from i_sc1 only above bit 0
  sc #(.P(8'h81), .B('{8})) i_sc81r ();  // Array parameter given last

  td #(
      .N(8),
      .V('{200, 100}),
      .P('{'{a: 200, b: 1}, '{a: 100, b: 2}}),
      .S('{a: 150, b: 3})
  ) i_td ();
  td #(.N(4), .V('{13, 10})) i_td4 ();

  initial begin
    // Overridden size
    `checkd(i_m2.N, 2);
    `checkd($size(i_m2.V), 2);
    `checkd($bits(i_m2.V), 2 * 32);
    `checkd(i_m2.V[0], 1);
    `checkd(i_m2.V[1], 2);

    `checkd($size(i_m3.V), 3);
    `checkd(i_m3.V[0], 1);
    `checkd(i_m3.V[1], 2);
    `checkd(i_m3.V[2], 3);

    // Size override that is not a folded constant
    `checkd($size(i_m3e.V), 3);
    `checkd(i_m3e.V[2], 3);

    // Size left at its default
    `checkd($size(i_m1.V), 1);
    `checkd(i_m1.V[0], 1);

    // Patterns that don't name every element individually
    `checkd($size(i_m4d.V), 4);
    `checkd(i_m4d.V[0], 1);
    `checkd(i_m4d.V[3], 1);
    `checkd($size(i_m3r.V), 3);
    `checkd(i_m3r.V[0], 1);
    `checkd(i_m3r.V[2], 1);

    // Pattern with its own type
    `checkd($size(i_m3t.V), 3);
    `checkd(i_m3t.V[2], 6);

    // Parameter-dependent element width
    `checkd($size(i_p.B), 2);
    `checkd($bits(i_p.B), 2 * 8);
    `checkh(i_p.B[0], 8'ha);
    `checkh(i_p.B[1], 8'hb);

    // Both dimensions parameter dependent
    `checkd($size(i_d2.V), 2);
    `checkd($size(i_d2.V[0]), 3);
    `checkd(i_d2.V[0][0], 1);
    `checkd(i_d2.V[1][2], 6);

    // Interface parameters
    `checkd($size(i_iface.V), 3);
    `checkd(i_iface.V[0], 1);
    `checkd(i_iface.V[2], 3);

    // Concatenation value against a parameter-dependent width
    `checkd($bits(i_c.P), 16);
    `checkh(i_c.P, 16'h0a0b);

    // Size from a type parameter
    `checkd($size(i_r.V), 16);
    `checkd($bits(i_r.V), 16 * 16);
    `checkd(i_r.V[0], 1);
    `checkd(i_r.V[15], 1);

    // Whole parameter type from a type parameter
    `checkd($bits(i_sn.V), 16);
    `checkh(i_sn.V.a, 8'h1);
    `checkh(i_sn.V.b, 8'h2);
    `checkd($bits(i_sw.V), 64);
    `checkh(i_sw.V.a, 32'h3);
    `checkh(i_sw.V.b, 32'h4);

    // Untyped parameter, parameter-dependent default value
    `checkd($size(i_u.LST), 8);
    `checkd($size(i_ud.LST), 8);

    // Size from the enclosing module's parameter
    `checkd($size(i_mid.i_pass.V), 3);
    `checkd(i_mid.i_pass.V[0], 1);
    `checkd(i_mid.i_pass.V[2], 3);
    `checkd($size(i_mid.i_expr.V), 4);
    `checkd(i_mid.i_expr.V[3], 4);

    // Zero default size
    `checkd($size(i_z1.V), 1);
    `checkd(i_z1.V[0], 9);
    `checkd($size(i_z3.V), 3);
    `checkd(i_z3.V[2], 7);
    `checkd($size(i_bt.i_bz.V), 2);
    `checkd(i_bt.i_bz.V[0], 4);
    `checkd(i_bt.i_bz.V[1], 99);

    // Size from another array parameter
    `checkd($size(i_eb.V), 2);
    `checkd(i_eb.V[1], 6);
    `checkd($size(i_ea.V), 2);
    `checkd(i_ea.V[1], 6);
    `checkd($size(i_ed.V), 1);
    `checkd(i_ed.V[0], 5);
    `checkd($size(i_sz.V), 3);
    `checkd(i_sz.V[2], 9);

    // Size from a localparam of the parameter port list
    `checkd($size(i_lp.V), 3);
    `checkd(i_lp.V[2], 3);
    `checkd($size(i_lpd.V), 4);

    // Sizes from values converted to the declared types
    `checkd($size(i_cv.B), 8);
    `checkd(i_cv.N, 1);
    `checkd($size(i_cv.T), 1);
    `checkd(i_cv.T[0], 2);
    `checkd(i_cv.S, -1);
    `checkd($size(i_cv.G), 2);
    `checkd(i_cv.G[1], 4);

    // Scalar width from an array parameter
    `checkd($bits(i_sc1.P), 8);
    `checkh(i_sc1.P, 8'h01);
    `checkd($bits(i_sc81.P), 8);
    `checkh(i_sc81.P, 8'h81);
    `checkd($bits(i_sc81r.P), 8);
    `checkh(i_sc81r.P, 8'h81);

    // Typedefs of the module
    `checkd($bits(i_td.V[0]), 8);
    `checkd(i_td.V[0], 200);
    `checkd(i_td.V[1], 100);
    `checkd($bits(i_td.P[0]), 12);
    `checkd(i_td.P[0].a, 200);
    `checkd(i_td.P[1].b, 2);
    `checkd($bits(i_td.S), 12);
    `checkd(i_td.S.a, 150);
    `checkd($bits(i_td.x), 12);
    `checkd($bits(i_td4.V[0]), 4);
    `checkd(i_td4.V[0], 13);
    `checkd($bits(i_td4.x), 8);

    // Class-scoped references
    `checkd(cls#(.N(2), .V('{1, 2}))::last(), 2);
    `checkd(cls3_t::last(), 6);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
