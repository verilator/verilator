// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// Overrides of unpacked structure parameters, and of unpacked arrays of them, with each
// instance checking the values, widths and generate choices it was given.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package cfg_pkg;
  typedef struct {
    int a;
    byte b;
  } sub_t;
  typedef struct {
    bit en;
    int w;
    sub_t sub;
  } cfg_t;
  localparam cfg_t CFG_DEFAULT = '{en: 1'b1, w: 33, sub: '{a: 5, b: 6}};
  localparam cfg_t CFG_PKG = '{en: 1'b0, w: 7, sub: '{a: 11, b: -12}};
  localparam cfg_t CFGS_PKG[2] = '{CFG_PKG, '{en: 1'b1, w: 95, sub: '{a: 51, b: 52}}};
endpackage

// Given a nested structure
module leaf_sub #(
    parameter cfg_pkg::sub_t SUB = '{a: 0, b: 0},
    parameter int EXP_A = 0,
    parameter int EXP_B = 0
) ();
  initial begin
    `checkd(SUB.a, EXP_A);
    `checkd(int'(SUB.b), EXP_B);
  end
endmodule

// Given a whole structure
module leaf #(
    parameter cfg_pkg::cfg_t CFG = cfg_pkg::CFG_DEFAULT,
    parameter bit EXP_EN = 1'b1,
    parameter int EXP_W = 33,
    parameter int EXP_A = 5,
    parameter int EXP_B = 6
) ();
  logic [CFG.w-1:0] q;
  localparam int SUB_A = CFG.sub.a;
  if (CFG.en) begin : g_en
    initial `checkd(EXP_EN, 1'b1);
  end
  else begin : g_dis
    initial `checkd(EXP_EN, 1'b0);
  end
  initial begin
    `checkd(CFG.en, EXP_EN);
    `checkd(CFG.w, EXP_W);
    `checkd($bits(q), EXP_W);
    `checkd(SUB_A, EXP_A);
    `checkd(int'(CFG.sub.b), EXP_B);
  end
  leaf_sub #(
      .SUB(CFG.sub),
      .EXP_A(EXP_A),
      .EXP_B(EXP_B)
  ) u_sub ();
endmodule

// Given structure members
module leaf_member #(
    parameter bit EN = 1'b1,
    parameter int W = 1,
    parameter int A = 0,
    parameter bit EXP_EN = 1'b1,
    parameter int EXP_W = 33,
    parameter int EXP_A = 5
) ();
  logic [W-1:0] q;
  initial begin
    `checkd(EN, EXP_EN);
    `checkd($bits(q), EXP_W);
    `checkd(A, EXP_A);
  end
endmodule

// Given an array of structures, passing elements and members down
module core #(
    parameter int N = 2,
    parameter cfg_pkg::cfg_t CFGS[N] = '{default: cfg_pkg::CFG_DEFAULT},
    parameter bit EXP_EN[N] = '{default: 1'b1},
    parameter int EXP_W[N] = '{default: 33},
    parameter int EXP_A[N] = '{default: 5},
    parameter int EXP_B[N] = '{default: 6}
) ();
  for (genvar n = 0; n < N; ++n) begin : g_if
    logic [CFGS[n].w-1:0] d;
    if (CFGS[n].en) begin : g_en
      initial `checkd(EXP_EN[n], 1'b1);
    end
    else begin : g_dis
      initial `checkd(EXP_EN[n], 1'b0);
    end
    initial `checkd($bits(d), EXP_W[n]);
    leaf #(
        .CFG(CFGS[n]),
        .EXP_EN(EXP_EN[n]),
        .EXP_W(EXP_W[n]),
        .EXP_A(EXP_A[n]),
        .EXP_B(EXP_B[n])
    ) u_leaf ();
    leaf_member #(
        .EN(CFGS[n].en),
        .W(CFGS[n].w),
        .A(CFGS[n].sub.a),
        .EXP_EN(EXP_EN[n]),
        .EXP_W(EXP_W[n]),
        .EXP_A(EXP_A[n])
    ) u_member ();
  end
endmodule

module t;
  localparam cfg_pkg::cfg_t CFG_LOCAL = '{en: 1'b0, w: 65, sub: '{a: 21, b: 22}};
  localparam cfg_pkg::cfg_t CFGS[3] = '{
      cfg_pkg::CFG_DEFAULT,
      '{en: 1'b0, w: 15, sub: '{a: 31, b: 32}},
      CFG_LOCAL
  };

  // Single structure
  leaf u_default ();
  leaf #(.CFG(cfg_pkg::CFG_DEFAULT)) u_default_explicit ();
  leaf #(
      .CFG('{en: 1'b0, w: 7, sub: '{a: 1, b: 2}}),
      .EXP_EN(1'b0),
      .EXP_W(7),
      .EXP_A(1),
      .EXP_B(2)
  ) u_named ();
  leaf #(
      .CFG('{1'b1, 9, '{3, 4}}),
      .EXP_W(9),
      .EXP_A(3),
      .EXP_B(4)
  ) u_positional ();
  leaf #(
      .CFG('{default: 0, w: 31, sub: '{default: 8}}),
      .EXP_EN(1'b0),
      .EXP_W(31),
      .EXP_A(8),
      .EXP_B(8)
  ) u_default_key ();
  leaf #(
      .CFG(CFG_LOCAL),
      .EXP_EN(1'b0),
      .EXP_W(65),
      .EXP_A(21),
      .EXP_B(22)
  ) u_local ();
  leaf #(
      .CFG(cfg_pkg::CFG_PKG),
      .EXP_EN(1'b0),
      .EXP_W(7),
      .EXP_A(11),
      .EXP_B(-12)
  ) u_pkg ();
  leaf #(
      .CFG(CFGS[1]),
      .EXP_EN(1'b0),
      .EXP_W(15),
      .EXP_A(31),
      .EXP_B(32)
  ) u_elem ();

  // Array of structures
  core u_core_default ();
  core #(
      .N(3),
      .CFGS(CFGS),
      .EXP_EN('{1'b1, 1'b0, 1'b0}),
      .EXP_W('{33, 15, 65}),
      .EXP_A('{5, 31, 21}),
      .EXP_B('{6, 32, 22})
  ) u_core_local ();
  core #(
      .CFGS('{'{en: 1'b0, w: 63, sub: '{a: 41, b: 42}}, cfg_pkg::CFG_PKG}),
      .EXP_EN('{1'b0, 1'b0}),
      .EXP_W('{63, 7}),
      .EXP_A('{41, 11}),
      .EXP_B('{42, -12})
  ) u_core_inline ();
  core #(
      .CFGS(cfg_pkg::CFGS_PKG),
      .EXP_EN('{1'b0, 1'b1}),
      .EXP_W('{7, 95}),
      .EXP_A('{11, 51}),
      .EXP_B('{-12, 52})
  ) u_core_pkg ();

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
