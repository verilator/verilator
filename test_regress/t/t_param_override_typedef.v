// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Scalar overrides of parameters typed by a type declared in the module (bug 1)

module m_fixed;
  typedef logic [4:0] word_t;
  parameter word_t B = 0;
  localparam int BITS = $bits(B);
endmodule

module m_dep;
  parameter int W = 4;
  typedef logic [W-1:0] word_t;
  parameter word_t B = 0;
  localparam int BITS = $bits(B);
endmodule

module m_enum;
  parameter int W = 4;
  typedef enum logic [W-1:0] {
    X = 0,
    Y = 9
  } e_t;
  // verilator lint_off ENUMVALUE
  parameter e_t E = X;
  // verilator lint_on ENUMVALUE
  localparam int BITS = $bits(E);
endmodule

module m_lparam;
  parameter int W = 4;
  localparam int L = W * 2;
  typedef logic [L-1:0] word_t;
  parameter word_t B = 0;
  localparam int BITS = $bits(B);
endmodule

module m_alias;  // Typedef of a type parameter
  parameter type T = logic [3:0];
  typedef T alias_t;
  parameter alias_t B = 0;
  localparam int BITS = $bits(B);
endmodule

module m_packed;  // Packed array of a typedef
  parameter int W = 4;
  typedef logic [W-1:0] w_t;
  parameter w_t [1:0] B = 0;
  localparam int BITS = $bits(B);
endmodule

module m_su;  // Struct and union typedefs
  parameter int W = 4;
  typedef struct packed {
    logic [W-1:0] hi;
    logic [W-1:0] lo;
  } s_t;
  typedef union packed {
    logic [W-1:0] a;
    logic [W-1:0] b;
  } u_t;
  parameter s_t S = '0;
  parameter u_t U = '0;
  localparam int SBITS = $bits(S);
  localparam int UBITS = $bits(U);
endmodule

module m_str;
  typedef string str_t;
  parameter str_t S = "x";
endmodule

// Equal values written differently must give one specialization, as virtual interface
// types are compared by specialization
interface i_vif #(
    parameter logic [7:0] W = 8'd4
);
  logic [W-1:0] d;
endinterface

interface i_dep;
  parameter int W = 4;
  typedef logic [W-1:0] word_t;
  parameter word_t B = 0;
  localparam int BITS = $bits(B);
endinterface

module t;
  m_fixed #(.B(5'd17)) u_fixed ();
  m_dep u_dep_default ();
  m_dep #(
      .W(8),
      .B(8'd200)
  ) u_dep8 ();
  m_dep #(
      .W(4),
      .B(4'd9)
  ) u_dep4 ();
  // verilator lint_off ENUMVALUE
  m_enum #(
      .W(8),
      .E(8'd200)
  ) u_enum8 ();
  // verilator lint_on ENUMVALUE
  m_lparam #(
      .W(8),
      .B(16'd200)
  ) u_lparam8 ();
  i_dep #(
      .W(8),
      .B(8'd200)
  ) i_dep8 ();
  m_dep #(
      .W(8),
      .B(200)
  ) u_dep8_unsized ();
  m_alias #(
      .T(logic [7:0]),
      .B(8'd200)
  ) u_alias8 ();
  m_alias #(.B(4'd9)) u_alias4 ();
  m_packed #(
      .W(8),
      .B(16'hcafe)
  ) u_packed8 ();
  m_str #(.S("hello")) u_str ();
  m_su #(
      .W(8),
      .S(16'hcafe),
      .U(8'hab)
  ) u_su8 ();
  i_vif #(.W(8)) u_vif ();
  virtual i_vif #(.W(8'd8)) vif8;
  m_dep u_defparam ();
  defparam u_defparam.W = 8; defparam u_defparam.B = 8'd200;

  initial begin
    `checkd(u_fixed.B, 17);
    `checkd(u_fixed.BITS, 5);
    `checkd(u_dep_default.B, 0);
    `checkd(u_dep_default.BITS, 4);
    `checkd(u_dep8.B, 200);
    `checkd(u_dep8.BITS, 8);
    `checkd(u_dep4.B, 9);
    `checkd(u_dep4.BITS, 4);
    `checkd(u_enum8.E, 200);
    `checkd(u_enum8.BITS, 8);
    `checkd(u_lparam8.B, 200);
    `checkd(u_lparam8.BITS, 16);
    `checkd(i_dep8.B, 200);
    `checkd(i_dep8.BITS, 8);
    `checkd(u_dep8_unsized.B, 200);
    `checkd(u_dep8_unsized.BITS, 8);
    `checkd(u_alias8.B, 200);
    `checkd(u_alias8.BITS, 8);
    `checkd(u_alias4.B, 9);
    `checkd(u_alias4.BITS, 4);
    `checkd(u_packed8.B, 16'hcafe);
    `checkd(u_packed8.BITS, 16);
    `checks(u_str.S, "hello");
    `checkd(u_su8.S, 16'hcafe);
    `checkd(u_su8.SBITS, 16);
    `checkd(u_su8.U, 8'hab);
    `checkd(u_su8.UBITS, 8);
    vif8 = u_vif;
    `checkd($bits(vif8.d), 8);
    `checkd(u_defparam.B, 200);
    `checkd(u_defparam.BITS, 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
