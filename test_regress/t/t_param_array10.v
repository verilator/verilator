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

// Concatenation as the value of a parameter with a parameter-dependent width.
// A concat is self-determined, so it does not go through the port's type, but
// check it here as it is the closest relative of an assignment pattern.
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

// Size from a parameter declared after the array's own parameter
module q #(
    parameter int V[N] = '{0},
    parameter int N = 1
) ();
endmodule

// Size from a type parameter
module r #(
    parameter type T = byte,
    parameter T V[$bits(T)] = '{default: 0}
) ();
endmodule

// Whole port type is a type parameter, so the substituted type replaces the
// root of the port's type rather than a range inside it
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

  m #(.N(2), .V('{1, 2})) i_m2 ();
  m #(.N(3), .V('{1, 2, 3})) i_m3 ();
  m #(.N(TWO + 1), .V('{1, 2, 3})) i_m3e ();  // Non-folded size override
  m #(.V('{1})) i_m1 ();  // Size left at its default
  m #(.N(4), .V('{default: 1})) i_m4d ();  // Default in the pattern
  m #(.N(3), .V('{3{1}})) i_m3r ();  // Replication in the pattern

  p #(.W(8), .B('{8'ha, 8'hb})) i_p ();

  d2 #(.N(2), .M(3), .V('{'{1, 2, 3}, '{4, 5, 6}})) i_d2 ();

  iface #(.N(3), .V('{1, 2, 3})) i_iface ();

  c #(.W(16), .P({8'ha, 8'hb})) i_c ();

  q #(.N(2), .V('{1, 2})) i_q2 ();

  r #(.T(shortint), .V('{16{1}})) i_r ();

  s #(.T(narrow_t), .V('{a: 8'h1, b: 8'h2})) i_sn ();
  s #(.V('{a: 32'h3, b: 32'h4})) i_sw ();  // Type left at its default

  u #(.LEN(8), .LST('{8{0}})) i_u ();
  u #(.LEN(8)) i_ud ();  // Default value must resize with LEN

  mid #(.M(3), .W('{1, 2, 3})) i_mid ();

  initial begin
    // Overridden size
    if (i_m2.N != 2) $stop;
    if ($size(i_m2.V) != 2) $stop;
    if ($bits(i_m2.V) != 2 * 32) $stop;
    if (i_m2.V[0] != 1 || i_m2.V[1] != 2) $stop;

    if ($size(i_m3.V) != 3) $stop;
    if (i_m3.V[0] != 1 || i_m3.V[1] != 2 || i_m3.V[2] != 3) $stop;

    // Size override that is not a folded constant
    if ($size(i_m3e.V) != 3) $stop;
    if (i_m3e.V[2] != 3) $stop;

    // Size left at its default
    if ($size(i_m1.V) != 1) $stop;
    if (i_m1.V[0] != 1) $stop;

    // Patterns that don't name every element individually
    if ($size(i_m4d.V) != 4) $stop;
    if (i_m4d.V[0] != 1 || i_m4d.V[3] != 1) $stop;
    if ($size(i_m3r.V) != 3) $stop;
    if (i_m3r.V[0] != 1 || i_m3r.V[2] != 1) $stop;

    // Parameter-dependent element width
    if ($size(i_p.B) != 2) $stop;
    if ($bits(i_p.B) != 2 * 8) $stop;
    if (i_p.B[0] != 8'ha || i_p.B[1] != 8'hb) $stop;

    // Both dimensions parameter dependent
    if ($size(i_d2.V) != 2) $stop;
    if ($size(i_d2.V[0]) != 3) $stop;
    if (i_d2.V[0][0] != 1 || i_d2.V[1][2] != 6) $stop;

    // Interface parameters
    if ($size(i_iface.V) != 3) $stop;
    if (i_iface.V[0] != 1 || i_iface.V[2] != 3) $stop;

    // Concatenation value against a parameter-dependent width
    if ($bits(i_c.P) != 16) $stop;
    if (i_c.P != 16'h0a0b) $stop;

    // Size parameter declared after the array parameter
    if ($size(i_q2.V) != 2) $stop;
    if (i_q2.V[0] != 1 || i_q2.V[1] != 2) $stop;

    // Size from a type parameter
    if ($size(i_r.V) != 16) $stop;
    if ($bits(i_r.V) != 16 * 16) $stop;
    if (i_r.V[0] != 1 || i_r.V[15] != 1) $stop;

    // Whole port type from a type parameter
    if ($bits(i_sn.V) != 16) $stop;
    if (i_sn.V.a != 8'h1 || i_sn.V.b != 8'h2) $stop;
    if ($bits(i_sw.V) != 64) $stop;
    if (i_sw.V.a != 32'h3 || i_sw.V.b != 32'h4) $stop;

    // Untyped parameter, parameter-dependent default value
    if ($size(i_u.LST) != 8) $stop;
    if ($size(i_ud.LST) != 8) $stop;

    // Size from the enclosing module's parameter
    if ($size(i_mid.i_pass.V) != 3) $stop;
    if (i_mid.i_pass.V[0] != 1 || i_mid.i_pass.V[2] != 3) $stop;
    if ($size(i_mid.i_expr.V) != 4) $stop;
    if (i_mid.i_expr.V[3] != 4) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
