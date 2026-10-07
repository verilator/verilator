// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Assignment-pattern overrides typed in the specialization, not the template (bug 2)

package hp;
  typedef enum logic [1:0] {
    FmtA = 0,
    FmtB = 2,
    FmtC = 3
  } fmt_e;
  typedef struct packed {
    logic en;
    fmt_e fmt;
    logic [5:0] mask;
  } cfg_t;
  typedef struct packed {
    cfg_t c;
    logic [3:0] n;
  } outer_t;
  typedef struct packed {
    fmt_e k;
    logic [3:0] v;
  } leaf_t;
  typedef struct packed {
    leaf_t l0;
    leaf_t l1;
    logic [2:0] tag;
  } mid_t;
  typedef struct packed {
    mid_t m;
    logic [7:0] id;
  } top_t;
  typedef struct packed {
    int a;
    logic [3:0] b;
  } cnt_t;
endpackage

// Nested patterns whose inner types depend on an overridden parameter
module m_nest_dep;
  parameter int W = 4;
  typedef struct packed {logic [W-1:0] a;} in_t;
  parameter in_t ARR[2] = '{default: '0};
  typedef struct packed {
    in_t i;
    logic [W-1:0] b;
  } out_t;
  parameter out_t S = '0;
  localparam int BITS = $bits(S);
endmodule

// Nested pattern forms: deep nesting, inner default, replicated nested pattern,
// type key, positional nesting, array of arrays, struct localparam as a member
module m_nest #(
    parameter hp::top_t T = '0,
    parameter hp::mid_t MD = '0,
    parameter hp::leaf_t LR[4] = '{default: '0},
    parameter hp::cnt_t MT = '0,
    parameter hp::leaf_t LP[2] = '{default: '0},
    parameter logic [3:0] AA[2][3] = '{default: 0},
    parameter hp::mid_t ML = '0
);
endmodule

// Pattern members that are symbolic rather than literal
module m_sym #(
    parameter hp::cfg_t CFG = '0,
    parameter hp::outer_t O = '0,
    parameter hp::cfg_t ARR[2] = '{default: '0},
    parameter logic [7:0] R[4] = '{default: 0}
);
endmodule

module m_hdr #(
    parameter int W = 4,
    parameter logic [W-1:0] A[2] = '{default: 0}
);
  localparam int BITS = $bits(A[0]);
endmodule

module m_size #(  // Array size from another parameter
    parameter int N = 2,
    parameter int W = 4,
    parameter logic [W-1:0] A[N] = '{default: 0}
);
  localparam int SIZE = $size(A);
  localparam int BITS = $bits(A[0]);
endmodule

module m_elem #(  // Width from an element of an array parameter
    parameter byte B[1] = '{1},
    parameter logic [B[0]-1:0] P = '0,
    parameter int V[B[0]] = '{default: 0}
);
  localparam int BITS = $bits(P);
endmodule

interface i_hdr #(
    parameter int W = 4,
    parameter logic [W-1:0] A[2] = '{default: 0}
);
  localparam int BITS = $bits(A[0]);
endinterface

interface i_inner #(
    parameter int W = 4,
    parameter logic [W-1:0] A[2] = '{default: 0}
);
  localparam int BITS = $bits(A[0]);
endinterface

interface i_outer #(  // Builds an inner interface's pattern from its own parameter
    parameter int W = 4
);
  i_inner #(
      .W(W),
      .A('{W[W-1:0], W'(2 * W)})
  ) in ();
endinterface

module m_strreal #(
    parameter string S[2] = '{"x", "y"},
    parameter real R[2] = '{0.0, 0.0}
);
endmodule

module p_par #(  // Passes its own parameter into a pattern
    parameter int W = 4
);
  m_hdr #(
      .W(W),
      .A('{W[W-1:0], W'(2 * W)})
  ) u ();
endmodule

module m_tparam #(
    parameter type T = logic [3:0],
    parameter T A[2] = '{default: 0}
);
  localparam int BITS = $bits(A[0]);
endmodule

module m_body;
  parameter int W = 4;
  typedef logic [W-1:0] word_t;
  parameter word_t A[2] = '{default: 0};
  localparam int BITS = $bits(A[0]);
endmodule

module m_fixed;  // #8546
  typedef logic [4:0] word_t;
  parameter word_t A[2] = '{default: 0};
endmodule

module m_struct;
  parameter int W = 4;
  typedef struct packed {
    logic [W-1:0] a;
    logic [W-1:0] b;
  } s_t;
  parameter s_t S = '{a: 0, b: 0};
  localparam int BITS = $bits(S);
endmodule

class C_t #(  // Type parameter and pattern
    type T = logic [3:0],
    T A[2] = '{0, 0}
);
  static function int a1();
    return int'(A[1]);
  endfunction
  static function int bits();
    return $bits(A[0]);
  endfunction
endclass

class C #(
    int W = 4,
    logic [W-1:0] A[2] = '{0, 0}
);
  static function int a1();
    return int'(A[1]);
  endfunction
  static function int bits();
    return $bits(A[0]);
  endfunction
endclass

module t;
  m_hdr #(
      .W(8),
      .A('{8'd3, 8'd200})
  ) u_hdr8 ();
  m_hdr #(
      .W(4),
      .A('{4'd3, 4'd9})
  ) u_hdr4 ();
  m_tparam #(
      .T(logic [7:0]),
      .A('{8'd3, 8'd200})
  ) u_tparam8 ();
  m_body #(
      .W(8),
      .A('{8'd3, 8'd200})
  ) u_body8 ();
  m_fixed #(.A('{5'd3, 5'd17})) u_fixed ();
  m_size #(
      .N(3),
      .W(8),
      .A('{8'd10, 8'd20, 8'd30})
  ) u_size3 ();
  i_hdr #(
      .W(8),
      .A('{8'd3, 8'd200})
  ) i_hdr8 ();
  p_par #(.W(8)) u_par8 ();
  p_par #(.W(6)) u_par6 ();
  m_body #(
      .W(8),
      .A('{1, 2})
  ) u_body8_unsized ();
  m_hdr u_defparam ();
  defparam u_defparam.W = 8; defparam u_defparam.A =
  '{8'd3, 8'd200}
  ;
  i_outer #(.W(8)) i_outer8 ();
  m_strreal #(
      .S('{"aa", "bb"}),
      .R('{1.5, 2.5})
  ) u_strreal ();
  for (genvar i = 0; i < 3; i++) begin : gen
    m_hdr #(
        .W(5 + i),
        .A('{(5 + i)'(i), (5 + i)'(i + 10)})
    ) u ();
    initial begin
      `checkd(u.BITS, 5 + i);
      `checkd(u.A[1], i + 10);
    end
  end
  m_struct #(
      .W(8),
      .S('{a: 8'd3, b: 8'd200})
  ) u_struct8 ();
  localparam int P = 5;
  m_sym #(
      .CFG('{en: 1'b0, fmt: hp::FmtC, mask: '1}),
      .O('{c: '{en: 1'b1, fmt: hp::FmtB, mask: 6'd1}, n: 4'(P)}),
      .ARR('{'{en: 1'b0, fmt: hp::FmtA, mask: 6'd0}, '{en: 1'b1, fmt: hp::FmtC, mask: 6'd3}}),
      .R('{4{8'(P + 1)}})
  ) u_sym ();
  m_nest_dep #(
      .W(8),
      .S('{i: '{a: 8'd200}, b: 8'd100}),
      .ARR('{'{a: 8'd1}, '{a: 8'd250}})
  ) u_nd8 ();
  m_nest_dep #(
      .W(4),
      .S('{i: '{a: 4'd9}, b: 4'd3}),
      .ARR('{'{a: 4'd1}, '{a: 4'd2}})
  ) u_nd4 ();
  localparam hp::leaf_t LEAF = '{k: hp::FmtC, v: 4'd9};
  localparam int N = 3;
  m_nest #(
      .T(
      '{
          m: '{l0: '{k: hp::FmtB, v: 4'd1}, l1: '{k: hp::FmtC, v: 4'(N + 4)}, tag: 3'd5},
          id: 8'd200
      }
      ),
      .MD('{l0: '{k: hp::FmtC, default: '1}, l1: '{k: hp::FmtB, default: 4'd2}, tag: 3'd1}),
      .LR('{4{'{k: hp::FmtB, v: 4'd6}}}),
      .MT('{int : 70000, b: 4'd4}),
      .LP('{'{hp::FmtC, 4'd11}, '{hp::FmtB, 4'd12}}),
      .AA('{'{4'd1, 4'd2, 4'd3}, '{4'd4, 4'd5, 4'd6}}),
      .ML('{l0: LEAF, l1: '{k: hp::FmtA, v: 4'(N)}, tag: 3'd2})
  ) u_nest ();
  m_elem #(
      .P(1'b1),
      .V('{5})
  ) u_elem ();
  m_elem #(.P(1'b1)) u_elem_p ();
  // Instances differing only above bit 0 of P must not share a specialization
  m_elem #(
      .B('{4}),
      .P(4'b0011)
  ) u_elem3 ();
  m_elem #(
      .B('{4}),
      .P(4'b1011)
  ) u_elem11 ();
  localparam byte EB[1] = '{4};
  m_elem #(
      .B(EB),
      .P(4'b0011)
  ) u_elem_eb3 ();
  m_elem #(
      .B(EB),
      .P(4'b1011)
  ) u_elem_eb11 ();

  initial begin
    #1;
    `checkd(u_size3.SIZE, 3);
    `checkd(u_size3.BITS, 8);
    `checkd(u_size3.A[2], 30);
    `checkd(i_hdr8.A[1], 200);
    `checkd(i_hdr8.BITS, 8);
    `checkd(u_par8.u.A[1], 16);
    `checkd(u_par8.u.BITS, 8);
    `checkd(u_par6.u.A[1], 12);
    `checkd(u_par6.u.BITS, 6);
    `checkd(u_body8_unsized.A[1], 2);
    `checkd(u_body8_unsized.BITS, 8);
    `checkd(u_defparam.A[1], 200);
    `checkd(u_defparam.BITS, 8);
    `checkd(i_outer8.in.A[1], 16);
    `checkd(i_outer8.in.BITS, 8);
    `checks(u_strreal.S[1], "bb");
    `checkr(u_strreal.R[1], 2.5);
    `checkd((C_t#(logic [7:0], '{8'd3, 8'd200})::a1()), 200);
    `checkd((C_t#(logic [7:0], '{8'd3, 8'd200})::bits()), 8);
    `checkd(u_hdr8.A[1], 200);
    `checkd(u_hdr8.BITS, 8);
    `checkd(u_hdr4.A[1], 9);
    `checkd(u_hdr4.BITS, 4);
    `checkd(u_tparam8.A[1], 200);
    `checkd(u_tparam8.BITS, 8);
    `checkd(u_body8.A[1], 200);
    `checkd(u_body8.BITS, 8);
    `checkd(u_fixed.A[1], 17);
    `checkd(u_struct8.S.b, 200);
    `checkd(u_struct8.BITS, 16);
    `checkd(u_sym.CFG.fmt, 3);
    `checkd(u_sym.CFG.mask, 63);
    `checkd(u_sym.CFG.en, 0);
    `checkd(u_sym.O.c.fmt, 2);
    `checkd(u_sym.O.n, 5);
    `checkd(u_sym.ARR[1].fmt, 3);
    `checkd(u_sym.ARR[1].mask, 3);
    `checkd(u_sym.R[3], 6);
    `checkd(u_nd8.BITS, 16);
    `checkd(u_nd8.S.i.a, 200);
    `checkd(u_nd8.S.b, 100);
    `checkd(u_nd8.ARR[1].a, 250);
    `checkd(u_nd4.BITS, 8);
    `checkd(u_nd4.S.i.a, 9);
    `checkd(u_nd4.ARR[1].a, 2);
    `checkd(u_nest.T.m.l1.k, 3);
    `checkd(u_nest.T.m.l1.v, 7);
    `checkd(u_nest.T.m.tag, 5);
    `checkd(u_nest.T.id, 200);
    `checkd(u_nest.MD.l0.v, 15);
    `checkd(u_nest.MD.l1.k, 2);
    `checkd(u_nest.MD.l1.v, 2);
    `checkd(u_nest.LR[0].v, 6);
    `checkd(u_nest.LR[3].k, 2);
    `checkd(u_nest.MT.a, 70000);
    `checkd(u_nest.MT.b, 4);
    `checkd(u_nest.LP[0].k, 3);
    `checkd(u_nest.LP[1].v, 12);
    `checkd(u_nest.AA[0][2], 3);
    `checkd(u_nest.AA[1][0], 4);
    `checkd(u_nest.ML.l0.k, 3);
    `checkd(u_nest.ML.l0.v, 9);
    `checkd(u_nest.ML.l1.v, 3);
    `checkd((C#(8, '{8'd3, 8'd200})::a1()), 200);
    `checkd((C#(8, '{8'd3, 8'd200})::bits()), 8);
    `checkd(u_elem.BITS, 1);
    `checkd(u_elem.P, 1);
    `checkd(u_elem.V[0], 5);
    `checkd(u_elem_p.BITS, 1);
    `checkd(u_elem_p.P, 1);
    `checkd(u_elem3.BITS, 4);
    `checkd(u_elem3.P, 3);
    `checkd(u_elem11.P, 11);
    `checkd(u_elem_eb3.BITS, 4);
    `checkd(u_elem_eb3.P, 3);
    `checkd(u_elem_eb11.P, 11);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
