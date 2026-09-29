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
    parameter int N = 1,
    parameter int V[N] = '{0}
);
  static function int last();
    return V[N-1];
  endfunction
endclass

// Class parameter whose width comes from another, given after it in a typedef
class clw #(
    parameter int N = 1,
    parameter logic [N-1:0] P = '0
);
  static function int value();
    return int'(P);
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
  parameter elem_t W[2] = '{default: 0};  // Shares elem_t with V
  parameter pair_t P[2] = '{default: 0};
  parameter pair_t S = '0;
  pair_t x;
endmodule

// Array values converted to the parameter's element type
typedef byte unsigned ubyte1_t[1];
typedef int int1_t[1];
module ta #(
    parameter byte B[1] = '{1},
    parameter logic [(B[0] < 0 ? 8 : 1)-1:0] P = '0,
    parameter int V[B[0] < 0 ? 2 : B[0]] = '{default: 0}
) ();
endmodule

// The same, for instances made in the other order
module ta2 #(
    parameter byte B[1] = '{1},
    parameter logic [(B[0] < 0 ? 8 : 1)-1:0] P = '0
) ();
endmodule

// Sizes from one-bit parameters set by the unsized literal '1
module ub #(
    parameter logic [0:0] N = '1,
    parameter int A[N] = '{default: 0}
) ();
endmodule
module ui #(
    parameter N = '1,  // No type or range, so one bit
    parameter int A[N == 1 && $bits(N) == 1 ? 2 : 1] = '{default: 0}
) ();
endmodule
module us #(
    parameter logic N = '1,
    parameter logic [N+1:0] P = '0
) ();
endmodule
module us2 #(  // The same, for instances made in the other order
    parameter logic N = '1,
    parameter logic [N+1:0] P = '0
) ();
endmodule

// Sizes from real and type parameter typed values
module rv #(
    parameter real R = 1.0,
    parameter int A[$bits(R) / 16] = '{default: 0},
    parameter int D[R / 2 == 0.5 ? 2 : 1] = '{default: 0},
    parameter type T = byte,
    // verilator lint_off WIDTHTRUNC
    parameter T Q = 1,  // Overridden with a wider value
    // verilator lint_on WIDTHTRUNC
    parameter int E[$bits(Q)] = '{default: 0},
    parameter int F[Q] = '{default: 0}
) ();
endmodule

// Parameters signed or unsigned but without a type take the value's type
module sg #(
    parameter signed N = 1,
    parameter int A[N < 0 ? 2 : 1] = '{default: 0},
    parameter unsigned U = 1,
    parameter int B[U < 0 ? 1 : 2] = '{default: 0}
) ();
endmodule

// Size from a function of another parameter
module fn;
  parameter int N = 1;
  function automatic int f(input int x);
    return x + 1;
  endfunction
  parameter int V[f(N)] = '{default: 0};
endmodule

// Typedefs that share a dependency on a parameter, so resolving each once matters
module dg;
  parameter int N = 1;
  typedef logic [N-1:0] t0;
  typedef union packed {t0 a; t0 b;} t1;
  typedef union packed {t1 a; t1 b;} t2;
  typedef union packed {t2 a; t2 b;} t3;
  typedef union packed {t3 a; t3 b;} t4;
  typedef union packed {t4 a; t4 b;} t5;
  typedef union packed {t5 a; t5 b;} t6;
  typedef union packed {t6 a; t6 b;} t7;
  typedef union packed {t7 a; t7 b;} t8;
  typedef union packed {t8 a; t8 b;} t9;
  typedef union packed {t9 a; t9 b;} t10;
  typedef union packed {t10 a; t10 b;} t11;
  typedef union packed {t11 a; t11 b;} t12;
  typedef union packed {t12 a; t12 b;} t13;
  typedef union packed {t13 a; t13 b;} t14;
  typedef union packed {t14 a; t14 b;} t15;
  typedef union packed {t15 a; t15 b;} t16;
  typedef union packed {t16 a; t16 b;} t17;
  typedef union packed {t17 a; t17 b;} t18;
  typedef union packed {t18 a; t18 b;} t19;
  typedef union packed {t19 a; t19 b;} t20;
  typedef t20 top_t;
  parameter top_t V[2] = '{default: 0};
endmodule

// Sizes and types from $bits of a variable of a package or of the module, not a parameter
package pv;
  logic [4:0] sig5;
endpackage
module bv #(
    parameter int N = $bits(pv::sig5),
    parameter int V[N] = '{default: 0}
) ();
endmodule
module bp #(
    parameter type T = logic [$bits(pv::sig5)-1:0],
    parameter T V[2] = '{default: 0}
) ();
endmodule
module bw;
  logic [4:0] w5;
  typedef logic [$bits(w5)-1:0] w_t;
  parameter w_t V[2] = '{default: 0};
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
  localparam ULEN = 8;
  localparam logic [0:0] ALL = '1;
  localparam UALL = '1;
  localparam int SIZES[2] = '{4, 5};
  typedef int arr3_t[3];
  typedef cls#(.N(3), .V('{4, 5, 6})) cls3_t;
  typedef clw#(.P(8'h81), .N(TWO * 4)) clw81_t;  // Width given after the value
  typedef clw#(.P(8'h01), .N(TWO * 4)) clw01_t;  // Differs from clw81_t only above bit 0

  m #(.N(2), .V('{1, 2})) i_m2 ();
  m #(.N(3), .V('{1, 2, 3})) i_m3 ();
  m #(.N(TWO + 1), .V('{1, 2, 3})) i_m3e ();  // Non-folded size override
  m #(.V('{1})) i_m1 ();  // Size left at its default
  m #(.N(4), .V('{default: 1})) i_m4d ();  // Default in the pattern
  m #(.N(3), .V('{3{1}})) i_m3r ();  // Replication in the pattern
  m #(.N(3), .V(arr3_t'{4, 5, 6})) i_m3t ();  // Pattern with its own type
  m #(.N(), .V('{7})) i_me ();  // Empty override keeps the default

  p #(.W(8), .B('{8'ha, 8'hb})) i_p ();

  d2 #(.N(2), .M(3), .V('{'{1, 2, 3}, '{4, 5, 6}})) i_d2 ();

  iface #(.N(3), .V('{1, 2, 3})) i_iface ();

  c #(.W(16), .P({8'ha, 8'hb})) i_c ();

  r #(.T(shortint), .V('{16{1}})) i_r ();

  s #(.T(narrow_t), .V('{a: 8'h1, b: 8'h2})) i_sn ();
  s #(.V('{a: 32'h3, b: 32'h4})) i_sw ();  // Type left at its default

  u #(.LEN(8), .LST('{8{0}})) i_u ();
  u #(.LEN(8)) i_ud ();  // Default value must resize with LEN
  u #(.LEN(ULEN), .LST('{ULEN{1}})) i_uu ();  // Size from the enclosing module's parameter
  m #(.N(SIZES[1]), .V('{1, 2, 3, 4, 5})) i_m5s ();  // From an element of its array parameter

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
      .W('{55, 66}),
      .P('{'{a: 200, b: 1}, '{a: 100, b: 2}}),
      .S('{a: 150, b: 3})
  ) i_td ();
  td #(.N(4), .V('{13, 10})) i_td4 ();

  ta #(.B(ubyte1_t'{8'hff}), .P(8'h01), .V('{1, 2})) i_ta1 ();
  ta #(.B(ubyte1_t'{8'hff}), .P(8'h81), .V('{1, 2})) i_ta81 ();  // P differs only above bit 0
  ta2 #(.B(ubyte1_t'{8'hff}), .P(8'h81)) i_ta2_81 ();
  ta2 #(.B(ubyte1_t'{8'hff}), .P(8'h01)) i_ta2_1 ();
  ta #(.P(1'b1), .B(int1_t'{257}), .V('{5})) i_tb ();  // Truncated to a byte, so B[0] is 1

  ub #(.A('{7})) i_ub ();
  ub #(.N('1), .A('{8})) i_ubo ();
  ub #(.N(ALL), .A('{9})) i_ubp ();  // From the enclosing module's parameter
  ui #(.A('{1, 2})) i_ui ();
  ui #(.N('1), .A('{3, 4})) i_uio ();
  ui #(.N(UALL), .A('{5, 6})) i_uip ();
  us #(.P(3'b001)) i_us1 ();
  us #(.P(3'b101)) i_us5 ();  // P differs only above bit 0
  us2 #(.P(3'b101)) i_us2_5 ();
  us2 #(.P(3'b001)) i_us2_1 ();

  rv #(
      .R(1),
      .A('{4{1}}),
      .D('{1, 2}),
      .Q(257),
      .E('{8{1}}),
      .F('{9})
  ) i_rv ();
  rv #(.A('{4{1}}), .D('{1, 2}), .E('{8{1}}), .F('{9})) i_rvd ();  // Defaults
  rv #(
      .T(shortint),
      .Q(3),
      .A('{4{1}}),
      .D('{1, 2}),
      .E('{16{1}}),
      .F('{1, 2, 3})
  ) i_rvt ();

  sg #(.N(8'hff), .A('{1, 2}), .U(-1), .B('{3, 4})) i_sg ();

  fn #(.N(2), .V('{1, 2, 3})) i_fn ();

  dg #(.N(4), .V('{3, 5})) i_dg ();

  bv #(.V('{1, 2, 3, 4, 5})) i_bv ();
  bp #(.V('{17, 18})) i_bp ();
  bp #(.T(logic [$bits(pv::sig5):0]), .V('{33, 34})) i_bpo ();  // Type overridden
  bw #(.V('{17, 18})) i_bw ();

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

    // Empty override
    `checkd($size(i_me.V), 1);
    `checkd(i_me.V[0], 7);

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
    `checkd($size(i_uu.LST), 8);
    `checkd(i_uu.LST[7], 1);
    `checkd($size(i_m5s.V), 5);
    `checkd(i_m5s.V[4], 5);

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
    `checkd(i_td.W[1], 66);
    `checkd($bits(i_td.P[0]), 12);
    `checkd(i_td.P[0].a, 200);
    `checkd(i_td.P[1].b, 2);
    `checkd($bits(i_td.S), 12);
    `checkd(i_td.S.a, 150);
    `checkd($bits(i_td.x), 12);
    `checkd($bits(i_td4.V[0]), 4);
    `checkd(i_td4.V[0], 13);
    `checkd($bits(i_td4.x), 8);

    // Array values converted to the element type
    `checkd(i_ta1.B[0], -1);
    `checkd($bits(i_ta1.P), 8);
    `checkh(i_ta1.P, 8'h01);
    `checkd($size(i_ta1.V), 2);
    `checkh(i_ta81.P, 8'h81);
    `checkh(i_ta2_1.P, 8'h01);
    `checkh(i_ta2_81.P, 8'h81);
    `checkd(i_tb.B[0], 1);
    `checkd($bits(i_tb.P), 1);
    `checkd($size(i_tb.V), 1);

    // One-bit parameters from '1
    `checkd(i_ub.N, 1);
    `checkd($size(i_ub.A), 1);
    `checkd(i_ub.A[0], 7);
    `checkd($size(i_ubo.A), 1);
    `checkd(i_ubo.A[0], 8);
    `checkd($size(i_ubp.A), 1);
    `checkd(i_ubp.A[0], 9);
    `checkd($bits(i_ui.N), 1);
    `checkd($size(i_ui.A), 2);
    `checkd($size(i_uio.A), 2);
    `checkd($size(i_uip.A), 2);
    `checkd($bits(i_us1.P), 3);
    `checkd(i_us1.P, 1);
    `checkd(i_us5.P, 5);
    `checkd($bits(i_us2_1.P), 3);
    `checkd(i_us2_1.P, 1);
    `checkd(i_us2_5.P, 5);

    // Real and type parameter typed values
    `checkd($size(i_rv.A), 4);
    `checkd($size(i_rv.D), 2);
    `checkd($size(i_rv.E), 8);
    `checkd($size(i_rv.F), 1);
    `checkd($size(i_rvd.E), 8);
    `checkd($size(i_rvt.E), 16);
    `checkd($size(i_rvt.F), 3);

    // Signed or unsigned without a type
    `checkd($size(i_sg.A), 2);
    `checkd($size(i_sg.B), 2);

    // Size from a function
    `checkd($size(i_fn.V), 3);
    `checkd(i_fn.V[2], 3);

    // Typedefs sharing a dependency
    `checkd($bits(i_dg.V[0]), 4);
    `checkd(i_dg.V[1], 5);

    // Sizes and types from variables
    `checkd($size(i_bv.V), 5);
    `checkd(i_bv.V[4], 5);
    `checkd($bits(i_bp.V[0]), 5);
    `checkd(i_bp.V[1], 18);
    `checkd($bits(i_bpo.V[0]), 6);
    `checkd(i_bpo.V[1], 34);
    `checkd($bits(i_bw.V[0]), 5);
    `checkd(i_bw.V[1], 18);

    // Class-scoped references
    `checkd(cls#(.N(2), .V('{1, 2}))::last(), 2);
    `checkd(cls3_t::last(), 6);
    `checkh(clw81_t::value(), 'h81);
    `checkh(clw01_t::value(), 'h01);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
