// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
//  A parameter default can reference a parameter declared later, so they are
//  resolved in dependency order, not declaration order. Each case is present
//  as both a class and a module, and each is specialized three ways: with all
//  defaults, with the dependent parameter overridden, and with the parameter
//  it depends on overridden. All results are checked in the top level.
//
//  WARNING: This is not strictly IEEE compliant, which says that parameter
//  definitions can refer to earlier parameters (IEEE 1800-2023 6.20.1), but
//  supported here as some tools might accept them.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package Pkg;
  localparam int LP = 3;
  localparam type LT = int;
endpackage

typedef struct packed {
  logic [7:0] MEMBER;
} s_t;

//======================================================================
// Classes

// A type parameter default referencing a later declared type parameter
class ClsType #(
    type A = B,
    type B = int
);
  function int a_bits();
    return $bits(A);
  endfunction
endclass

// A value parameter default referencing a later declared value parameter
class ClsValue #(
    int A = B,
    int B = 1
);
  function int a_val();
    return int'(A);
  endfunction
endclass

// A range referencing a later declared value parameter
class ClsRange #(
    logic [B:0] A = 0,
    int B = 1
);
  function int a_bits();
    return $bits(A);
  endfunction
  function int a_val();
    return int'(A);
  endfunction
endclass

// A data type referencing a later declared type parameter
class ClsDType #(
    B A = 0,
    type B = int
);
  function int a_bits();
    return $bits(A);
  endfunction
  function int a_val();
    return int'(A);
  endfunction
endclass

// All of the above in a single parameter list
class ClsAll #(
    type TA = TB,
    int VA = VB,
    logic [VB:0] RA = 0,
    TB DA = 0,
    int VB = 1,
    type TB = int
);
  function int a_bits();
    return $bits(TA) + VA + $bits(RA) + $bits(DA);
  endfunction
endclass

// A chain, resolved in reverse declaration order
class ClsChain #(
    type A = B,
    type B = C,
    type C = shortint
);
  function int a_bits();
    return $bits(A);
  endfunction
endclass

// A nested class referencing parameters of the enclosing class. The dependent
// parameters are the inner class's, which cannot be overridden from outside
class ClsNest #(
    int N = 4,
    type T = int
);
  class Inner #(
      int M = N,
      type U = T
  );
    function int m_bits();
      return M + $bits(U);
    endfunction
  endclass
  Inner inner = new;
  function int n_bits();
    return inner.m_bits();
  endfunction
endclass

// '::' references to package localparams. Both parameters are dependent, as a
// package localparam cannot be overridden
class ClsPkg #(
    int N = Pkg::LP,
    type T = Pkg::LT
);
  function int n_bits();
    return N + $bits(T);
  endfunction
endclass

// References to earlier parameters in the same list, of both kinds
class ClsBack #(
    int A = 1,
    int B = A,
    type T = int,
    type U = T,
    logic [A:0] R = 0,
    U V = 0
);
  function int b_bits();
    return B + $bits(U) + $bits(R) + $bits(V);
  endfunction
endclass

// An assignment pattern key is a member name of the pattern's type, not a
// parameter reference, even when a parameter of the same name is declared later
class ClsPatKey #(
    s_t P = '{MEMBER: 8'h1},
    logic [7:0] MEMBER = 3
);
  function int m_val();
    return int'(P.MEMBER) + int'(MEMBER);
  endfunction
endclass

// The value of an assignment pattern member is a reference, unlike the key
class ClsPatVal #(
    s_t P = '{MEMBER: VAL},
    logic [7:0] VAL = 3
);
  function int m_val();
    return int'(P.MEMBER) + int'(VAL);
  endfunction
endclass

//======================================================================
// Modules

module ModType #(
    type A = B,
    type B = int
);
  A a;
endmodule

module ModValue #(
    int A = B,
    int B = 1
);
  int a = A;
endmodule

module ModRange #(
    logic [B:0] A = 0,
    int B = 1
);
  logic [B:0] a = A;
endmodule

module ModDType #(
    B A = 0,
    type B = int
);
  B a = A;
endmodule

module ModAll #(
    type TA = TB,
    int VA = VB,
    logic [VB:0] RA = 0,
    TB DA = 0,
    int VB = 1,
    type TB = int
);
  TA ta;
  int va = VA;
  logic [VB:0] ra = RA;
  TB da = DA;
endmodule

module ModChain #(
    type A = B,
    type B = C,
    type C = shortint
);
  A a;
endmodule

module ModNest #(
    int N = 4,
    type T = int
);
  class Inner #(
      int M = N,
      type U = T
  );
    function int m_bits();
      return M + $bits(U);
    endfunction
  endclass
  Inner inner = new;
endmodule

module ModPkg #(
    int N = Pkg::LP,
    type T = Pkg::LT
);
  T t;
  int n = N;
endmodule

module ModBack #(
    int A = 1,
    int B = A,
    type T = int,
    type U = T,
    logic [A:0] R = 0,
    U V = 0
);
  int b = B;
  U v = V;
  logic [A:0] r = R;
endmodule

module ModPatKey #(
    s_t P = '{MEMBER: 8'h1},
    logic [7:0] MEMBER = 3
);
  logic [7:0] m = P.MEMBER + MEMBER;
endmodule

module ModPatVal #(
    s_t P = '{MEMBER: VAL},
    logic [7:0] VAL = 3
);
  logic [7:0] m = P.MEMBER + VAL;
endmodule

//======================================================================

module t;
  // Defaults, dependent parameter overridden, depended-on parameter overridden
  ClsType ct_d = new;
  ClsType #(.A(byte)) ct_dep = new;
  ClsType #(.B(shortint)) ct_nod = new;

  ClsValue cv_d = new;
  ClsValue #(.A(7)) cv_dep = new;
  ClsValue #(.B(5)) cv_nod = new;

  ClsRange cr_d = new;
  ClsRange #(.A(3)) cr_dep = new;
  ClsRange #(.B(3)) cr_nod = new;

  ClsDType cd_d = new;
  ClsDType #(.A(5)) cd_dep = new;
  ClsDType #(.B(byte)) cd_nod = new;

  ClsAll ca_d = new;
  ClsAll #(.TA(byte), .VA(4)) ca_dep = new;
  ClsAll #(.VB(3), .TB(byte)) ca_nod = new;

  ClsChain cc_d = new;
  ClsChain #(.A(int)) cc_dep = new;
  ClsChain #(.C(byte)) cc_nod = new;

  ClsNest cn_d = new;
  ClsNest #(.N(7)) cn_dep = new;
  ClsNest #(.T(byte)) cn_nod = new;

  ClsPkg cp_d = new;
  ClsPkg #(.N(10)) cp_dep = new;
  ClsPkg #(.T(byte)) cp_nod = new;

  ClsBack cb_d = new;
  ClsBack #(.B(5), .U(byte)) cb_dep = new;
  ClsBack #(.A(2), .T(shortint)) cb_nod = new;

  ClsPatKey cpk_d = new;
  ClsPatKey #(.P(8'h5)) cpk_dep = new;
  ClsPatKey #(.MEMBER(8'd10)) cpk_nod = new;

  ClsPatVal cpv_d = new;
  ClsPatVal #(.P(8'h2)) cpv_dep = new;
  ClsPatVal #(.VAL(8'd7)) cpv_nod = new;

  ModType mt_d ();
  ModType #(.A(byte)) mt_dep ();
  ModType #(.B(shortint)) mt_nod ();

  ModValue mv_d ();
  ModValue #(.A(7)) mv_dep ();
  ModValue #(.B(5)) mv_nod ();

  ModRange mr_d ();
  ModRange #(.A(3)) mr_dep ();
  ModRange #(.B(3)) mr_nod ();

  ModDType md_d ();
  ModDType #(.A(5)) md_dep ();
  ModDType #(.B(byte)) md_nod ();

  ModAll ma_d ();
  ModAll #(.TA(byte), .VA(4)) ma_dep ();
  ModAll #(.VB(3), .TB(byte)) ma_nod ();

  ModChain mc_d ();
  ModChain #(.A(int)) mc_dep ();
  ModChain #(.C(byte)) mc_nod ();

  ModNest mn_d ();
  ModNest #(.N(7)) mn_dep ();
  ModNest #(.T(byte)) mn_nod ();

  ModPkg mp_d ();
  ModPkg #(.N(10)) mp_dep ();
  ModPkg #(.T(byte)) mp_nod ();

  ModBack mb_d ();
  ModBack #(.B(5), .U(byte)) mb_dep ();
  ModBack #(.A(2), .T(shortint)) mb_nod ();

  ModPatKey mpk_d ();
  ModPatKey #(.P(8'h5)) mpk_dep ();
  ModPatKey #(.MEMBER(8'd10)) mpk_nod ();

  ModPatVal mpv_d ();
  ModPatVal #(.P(8'h2)) mpv_dep ();
  ModPatVal #(.VAL(8'd7)) mpv_nod ();

  initial begin
    `checkh(ct_d.a_bits(), 32);
    `checkh(ct_dep.a_bits(), 8);
    `checkh(ct_nod.a_bits(), 16);

    `checkh(cv_d.a_val(), 1);
    `checkh(cv_dep.a_val(), 7);
    `checkh(cv_nod.a_val(), 5);

    `checkh(cr_d.a_bits(), 2);
    `checkh(cr_d.a_val(), 0);
    `checkh(cr_dep.a_bits(), 2);
    `checkh(cr_dep.a_val(), 3);
    `checkh(cr_nod.a_bits(), 4);
    `checkh(cr_nod.a_val(), 0);

    `checkh(cd_d.a_bits(), 32);
    `checkh(cd_d.a_val(), 0);
    `checkh(cd_dep.a_bits(), 32);
    `checkh(cd_dep.a_val(), 5);
    `checkh(cd_nod.a_bits(), 8);
    `checkh(cd_nod.a_val(), 0);

    `checkh(ca_d.a_bits(), 67);
    `checkh(ca_dep.a_bits(), 46);
    `checkh(ca_nod.a_bits(), 23);

    `checkh(cc_d.a_bits(), 16);
    `checkh(cc_dep.a_bits(), 32);
    `checkh(cc_nod.a_bits(), 8);

    `checkh(cn_d.n_bits(), 36);
    `checkh(cn_dep.n_bits(), 39);
    `checkh(cn_nod.n_bits(), 12);

    `checkh(cp_d.n_bits(), 35);
    `checkh(cp_dep.n_bits(), 42);
    `checkh(cp_nod.n_bits(), 11);

    `checkh(cb_d.b_bits(), 67);
    `checkh(cb_dep.b_bits(), 23);
    `checkh(cb_nod.b_bits(), 37);

    `checkh(cpk_d.m_val(), 4);
    `checkh(cpk_dep.m_val(), 8);
    `checkh(cpk_nod.m_val(), 11);

    `checkh(cpv_d.m_val(), 6);
    `checkh(cpv_dep.m_val(), 5);
    `checkh(cpv_nod.m_val(), 14);

    `checkh($bits(mt_d.a), 32);
    `checkh($bits(mt_dep.a), 8);
    `checkh($bits(mt_nod.a), 16);

    `checkh(mv_d.a, 1);
    `checkh(mv_dep.a, 7);
    `checkh(mv_nod.a, 5);

    `checkh($bits(mr_d.a), 2);
    `checkh(mr_d.a, 0);
    `checkh($bits(mr_dep.a), 2);
    `checkh(mr_dep.a, 3);
    `checkh($bits(mr_nod.a), 4);
    `checkh(mr_nod.a, 0);

    `checkh($bits(md_d.a), 32);
    `checkh(md_d.a, 0);
    `checkh($bits(md_dep.a), 32);
    `checkh(md_dep.a, 5);
    `checkh($bits(md_nod.a), 8);
    `checkh(md_nod.a, 0);

    `checkh($bits(ma_d.ta) + ma_d.va + $bits(ma_d.ra) + $bits(ma_d.da), 67);
    `checkh($bits(ma_dep.ta) + ma_dep.va + $bits(ma_dep.ra) + $bits(ma_dep.da), 46);
    `checkh($bits(ma_nod.ta) + ma_nod.va + $bits(ma_nod.ra) + $bits(ma_nod.da), 23);

    `checkh($bits(mc_d.a), 16);
    `checkh($bits(mc_dep.a), 32);
    `checkh($bits(mc_nod.a), 8);

    `checkh(mn_d.inner.m_bits(), 36);
    `checkh(mn_dep.inner.m_bits(), 39);
    `checkh(mn_nod.inner.m_bits(), 12);

    `checkh(mp_d.n + $bits(mp_d.t), 35);
    `checkh(mp_dep.n + $bits(mp_dep.t), 42);
    `checkh(mp_nod.n + $bits(mp_nod.t), 11);

    `checkh(mb_d.b + $bits(mb_d.v) + $bits(mb_d.r) + $bits(mb_d.v), 67);
    `checkh(mb_dep.b + $bits(mb_dep.v) + $bits(mb_dep.r) + $bits(mb_dep.v), 23);
    `checkh(mb_nod.b + $bits(mb_nod.v) + $bits(mb_nod.r) + $bits(mb_nod.v), 37);

    `checkh(mpk_d.m, 4);
    `checkh(mpk_dep.m, 8);
    `checkh(mpk_nod.m, 11);

    `checkh(mpv_d.m, 6);
    `checkh(mpv_dep.m, 5);
    `checkh(mpv_nod.m, 14);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
