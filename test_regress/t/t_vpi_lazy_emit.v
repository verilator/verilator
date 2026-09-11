// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Generated-code shape under --vpi-lazy: residual member expansion, alias metadata rules.

// Non-ANSI split port: AstVar::combineType must propagate the lazy-VPI flag when merging
// the two declarations.
module sub(o, a);
  output o;
  logic [7:0] o;
  input [7:0] a;
  always_comb o = ~a;
endmodule

module t (
  input  logic                clk,
  input  logic                rst,
  input  logic [7:0]           a,
  input  logic [7:0]           in_a,
  input  logic [7:0]           in_b,
  input  logic signed  [7:0]   in_signed,
  input  logic         [7:0]   in_enum,
  input  logic signed [31:0]   in_int,
  input  logic         [7:0]   in_unsigned,
  input  logic         [7:0]   in_logic,
  output logic [7:0]           o_emit,
  output logic [7:0]           o_aliasmeta,
  output logic [7:0]           o_aliasdtype
);

  // emit: unpacked struct/array residual expansion in the symbol emitter
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;
  typedef struct { logic [7:0] m; logic [7:0] n; } us_t;

  us_t us_sig;
  us_t usarr [0:1];
  ps_t psarr [0:1];

  always_comb begin
    us_sig.m = a;
    us_sig.n = ~a;
    usarr[0].m = a;
    usarr[1].n = ~a;
    psarr[0].hi = a[3:0];
    psarr[1].lo = a[7:4];
  end

  logic [7:0] sub_o;
  sub subi(.o(sub_o), .a(a));

  assign o_emit = us_sig.m ^ usarr[0].m ^ {psarr[0].hi, psarr[1].lo} ^ sub_o;

  // aliasmeta: retargeted aliases; the VPI row must report the alias's own metadata
  logic [7:0] src_a;
  logic [7:0] src_b;

  always_ff @(posedge clk) begin
    if (rst) begin
      src_a <= 8'h0;
      src_b <= 8'h0;
    end else begin
      src_a <= in_a;
      src_b <= in_b;
    end
  end

  // Alias with a declared range differing from its canonical [7:0]
  logic [8:1] a_wide;  assign a_wide = src_a;
  // A packed-array alias of a reconstructed canonical: its row carries both packed dims
  logic [1:0][7:0] pa_src;
  always_comb begin pa_src[0] = src_a + 8'h1; pa_src[1] = src_a ^ 8'h2a; end
  logic [1:0][7:0] pa_ali;  assign pa_ali = pa_src;

  // Net alias of a reg canonical
  wire  [7:0] a_net;   assign a_net = src_b;

  assign o_aliasmeta = a_wide ^ a_net ^ pa_ali[0] ^ pa_ali[1];

  // alias_dtype: aliases with distinct dtypes but identical C storage
  typedef enum logic [7:0] { E_LO = 8'd10, E_MID = 8'd100, E_HI = 8'd200 } e_t;

  logic signed [7:0] signed_src;
  e_t                enum_var;
  integer            integer_var;
  logic        [7:0] unsigned_src;
  logic        [7:0] logic_src;

  always_ff @(posedge clk) begin
    signed_src   <= in_signed;
    enum_var     <= e_t'(in_enum);
    integer_var  <= in_int;
    unsigned_src <= in_unsigned;
    logic_src    <= in_logic;
  end

  // Bare-copy aliases
  logic        [7:0] a_sign;   assign a_sign  = signed_src;
  logic        [7:0] a_enum;   assign a_enum  = enum_var;
  int                a_ii;     assign a_ii    = integer_var;
  logic signed [7:0] a_ssign;  assign a_ssign = unsigned_src;
  bit          [7:0] a_bit;    assign a_bit   = logic_src;

  // Only a dtype-equivalent alias of a reconstructed canonical may be substituted into a cone;
  // a_diff differs in sign, so it is pinned as a cone boundary and keeps an entry of its own
  logic        [7:0] comb_src; assign comb_src = unsigned_src ^ 8'h3c;
  logic        [7:0] a_same;   assign a_same  = comb_src;
  logic signed [7:0] a_diff;   assign a_diff  = comb_src;
  logic        [7:0] cone_same; assign cone_same = a_same ^ 8'h5a;
  logic        [7:0] cone_diff; assign cone_diff = a_diff ^ 8'h5a;

  // Aliases that share comb_src's descriptor unread, so the shared row must still carry each
  // alias's own signed/bit/net metadata rather than the canonical's
  logic signed [7:0] s_sign;   assign s_sign  = comb_src;
  bit          [7:0] s_bit;    assign s_bit   = comb_src;
  wire         [7:0] s_net;    assign s_net   = comb_src;

  assign o_aliasdtype = signed_src ^ enum_var ^ integer_var[7:0] ^ unsigned_src ^ logic_src
                      ^ s_sign ^ s_bit ^ s_net;

endmodule
