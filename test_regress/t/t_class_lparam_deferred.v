// DESCRIPTION: Verilator: Verilog Test module
//
// Consumers of a class-scope-resolved localparam (typedef alias of a
// parameterized class, e.g. inst::b).  V3LinkDot defers the inst::b Dot until
// post-V3Param, so V3Param must resolve the deferred Dot everywhere such a
// value can be consumed - following VarRef chains into deferred lparams, and
// descending through typedefs and ParamTypeDTypes to reach buried Dots:
//   (1) module and interface instance parameter pins
//   (2) generate-for / -if / -case conditions
//   (3) typedef ranges, class type args, and $bits of class-scope typedefs
//   (4) nested class hierarchies (B2::width = inner_a::v)
//   (5) struct localparam field access (CFG::cfg.jt.cam_type)
//   (6) struct members typed by a class-scope typedef (CFG::data_t)
//   (7) `localparam type` bound to a child module's type parameter
//
// Plain localparam value chains are covered by t_class_lparam_chain.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct packed {
  logic [7:0] cam_type;
  logic [7:0] depth;
} inner_t;

typedef struct packed {
  inner_t     jt;
  logic [7:0] tag;
} cfg_t;

package pkg;
  virtual class C #(parameter int W = 1);
    typedef logic [W-1:0] data_t;
  endclass
endpackage

// Struct localparam whose fields derive from the class parameter, plus a
// wrapper class whose own lparam reads a nested struct field.
class SC #(parameter int W = 1);
  localparam cfg_t cfg = '{jt: '{cam_type: W[7:0], depth: W[7:0] + 8'd1},
                           tag: W[7:0] + 8'd2};
endclass

class SD #(parameter int W = 1);
  typedef SC#(W) CC;
  localparam int q = int'(CC::cfg.tag) + 100;
endclass

class P #(parameter cfg_t p = '{default: 0});
  localparam cfg_t pp = p;
endclass

module Sub #(parameter int WIDTH = 0) ();
endmodule

// Two-level: outer module forwards its param to an inner cell, so the
// deferred lparam value must flow through the cell-deparam chain.
module SubL1 #(parameter int W = 0) ();
  Sub #(W) inner ();
endmodule

interface SubIface #(parameter int IW = 1) ();
  logic [IW-1:0] data;
endinterface

// Takes an interface port - must elaborate after the iface cell pin is
// fully constified.
module Consumer (SubIface si);
endmodule

// Presence is observable, to confirm each generate flavour elaborated.
module Tag #(parameter int ID = 0) ();
endmodule

module Sink #(parameter int BITS = 1) ();
  logic [BITS-1:0] data;
endmodule

// Parameterized wrapper so the class specialization is deferred until
// V3Param processes the cell instance.
module Mid #(parameter int W = 8) ();
  typedef SC#(W) CFG;
  // (5) single-level struct field access, then nested (lsb accumulation)
  Sub #(int'(CFG::cfg.tag)) u_tag ();
  Sub #(int'(CFG::cfg.jt.cam_type)) u_cam ();
  Sub #(int'(CFG::cfg.jt.depth)) u_depth ();
  // nested struct-field Dot buried in a wrapper class's lparam value
  typedef SD#(W) DD;
  Sub #(int'(DD::q)) u_q ();

  // (6) struct member typed by a class-scope typedef from a parameterized
  // class, consumed by $bits on a cell pin.  Without following typedefs the
  // member RefDType stays unlinked and $bits trips an internal error.
  typedef pkg::C#(W) PCFG;
  typedef struct packed {
    PCFG::data_t payload;
    logic        v;
  } wrap_t;
  Sink #(.BITS($bits(wrap_t))) u_sink ();
endmodule

module PairHolder #(parameter cfg_t cfg = '{default: 0}) ();
  typedef P#(cfg) PALIAS;
  localparam logic [7:0] tag_val = PALIAS::pp.tag;
  localparam logic [7:0] cam_val = PALIAS::pp.jt.cam_type;
endmodule

// (7) The pin's RefDType has no typedefp() to follow - it points at the
// enclosing ParamTypeDType - so the deferred walk must descend refDTypep().
module TChild #(parameter type T = logic, parameter int EXP = 1) (input T a_i);
  initial `checkh($bits(T), EXP);
endmodule

module TFwd #(parameter type T = logic, parameter int EXP = 1) ();
  TChild #(.T(T), .EXP(EXP)) u (.a_i('0));
endmodule

module t;
  virtual class C #(parameter int a = 0);
    localparam int b = a;
    typedef logic [a-1:0] inner_t;
    // localparam derived from a typedef inside the same class
    localparam int width = $bits(inner_t);
  endclass

  // Two-level: B2's lparam value contains a class::member Dot of its own
  virtual class A2 #(parameter int x = 0);
    localparam int v = x * 2;
  endclass
  virtual class B2 #(parameter int y = 0);
    typedef A2#(y + 1) inner_a;
    localparam int width = inner_a::v;  // nested Dot inside B2's lparam
    // `sib` is deferred (holds the Dot); `sib_use` reads it as a sibling, so
    // the sibling must be folded before this member's value can constify.
    localparam int sib = inner_a::v;
    localparam int sib_use = sib + 1;
  endclass
  // Three-level: C2 wraps B2 wraps A2
  virtual class C2 #(parameter int z = 0);
    typedef B2#(z * 3) inner_b;
    localparam int total = inner_b::width;  // double-nested Dot
  endclass

  typedef C#(3) c3;
  typedef C#(4) c4;
  typedef C#(5) c5;
  typedef C#(8) c8;
  typedef C#(13) c13;
  typedef B2#(5) BInst;
  typedef C2#(2) CInst;

  // Deferred lparams (value contains a class::member Dot)
  localparam int b3 = c3::b;
  localparam int b4 = c4::b;
  localparam int b5 = c5::b;
  localparam int b8 = c8::b;
  localparam int b13 = c13::b;
  // Chained: value references another deferred lparam
  localparam int c8_ref = b8;
  localparam int d8_ref = c8_ref + 1;

  // (4) nested class hierarchies
  localparam int two_level = BInst::width;  // = A2#(6)::v = 12
  localparam int three_level = CInst::total;  // = B2#(6)::width = A2#(7)::v = 14
  localparam int nested_chain = BInst::width;

  // (1) module pins: bare VarRef, multi-lparam chain, expressions, a Dot
  // mixed with an lparam, two-level forwarding, and nested-class Dots.
  Sub #(b8) m_bare ();
  Sub #(d8_ref) m_chain ();
  Sub #(b4 + b5) m_expr ();
  Sub #(c4::b + b5) m_mix ();
  SubL1 #(b8) m_l1 ();
  Sub #(BInst::width) m_pin_direct ();
  Sub #(CInst::total) m_pin_deep ();
  Sub #(BInst::width + 1) m_pin_expr ();
  Sub #(nested_chain) m_pin_chain ();
  // sibling-lparam fold: BInst::sib_use = A2#(6)::v + 1 = 13
  Sub #(BInst::sib_use) m_pin_sibling ();

  // (1) interface pins, plus an iface bound to a module port
  SubIface #(b8) i_bare ();
  SubIface #(c8_ref) i_chain ();
  SubIface #(b8 + b13) i_expr ();
  Consumer cons (.si(i_bare));

  // (2) generate-for / -if / -case driven by deferred lparams
  for (genvar i = 0; i < b3; i++) begin : gf
    Tag #(100 + i) inst ();
  end
  if (b5 > b3) begin : gi_t
    Tag #(200) inst ();
  end else begin : gi_f
    Tag #(201) inst ();
  end
  case (b5)
    3: begin : gc Tag #(303) inst (); end
    5: begin : gc Tag #(305) inst (); end
    default: begin : gc Tag #(399) inst (); end
  endcase

  // (3) typedef range from a deferred lparam; class type-arg using a
  // deferred lparam; class-scope typedef via $bits; and a typedef whose
  // packed range is built from class-scope Dots directly (no lparam).
  typedef logic [b8-1:0] data_t;
  data_t data_value;
  typedef C#(b8) c_from_def;
  localparam int from_def_b = c_from_def::b;
  localparam int via_bits = c8::width;
  logic [b8-1:0] wide_bus;
  typedef logic [(c8::b + c8::b - 1):0] direct_use_t;
  Sub #(.WIDTH($bits(direct_use_t))) u_sub ();

  // (5)/(6) struct field access and class-scope-typed struct members
  Mid #(.W(8)) u_mid ();
  PairHolder #(.cfg('{jt: '{cam_type: 8'd7, depth: 8'd3}, tag: 8'd11})) u_ph ();

  // (7) `localparam type` from a class typedef, bound to a type parameter
  localparam type t_plain = pkg::C#(12)::data_t;
  typedef pkg::C#(9) alias_c;
  localparam type t_alias = alias_c::data_t;
  TChild #(.T(t_plain), .EXP(12)) u_plain (.a_i('0));
  TChild #(.T(cfg_t), .EXP(24)) u_tstruct (.a_i('0));
  TChild #(.T(t_alias), .EXP(9)) u_alias (.a_i('0));
  TFwd #(.T(t_plain), .EXP(12)) u_fwd ();

  initial begin
    `checkh(b3, 32'd3);
    `checkh(b4, 32'd4);
    `checkh(b5, 32'd5);
    `checkh(b8, 32'd8);
    `checkh(b13, 32'd13);
    `checkh(c8_ref, 32'd8);
    `checkh(d8_ref, 32'd9);
    // (1) interface pins took the deferred widths
    `checkh($bits(i_bare.data), 32'd8);
    `checkh($bits(i_chain.data), 32'd8);
    `checkh($bits(i_expr.data), 32'd21);
    // (3) typedefs / $bits
    `checkh(from_def_b, 32'd8);
    `checkh(via_bits, 32'd8);
    data_value = '1;
    `checkh(data_value, 8'hff);
    wide_bus = '1;
    `checkh(wide_bus, 8'hff);
    `checkh($bits(direct_use_t), 32'd16);
    // (4) nested classes
    `checkh(two_level, 32'd12);
    `checkh(three_level, 32'd14);
    `checkh(nested_chain, 32'd12);
    `checkh(m_pin_sibling.WIDTH, 32'd13);
    // (5) struct fields: tag = W+2, cam_type = W, depth = W+1
    `checkh(u_mid.u_tag.WIDTH, 32'd10);
    `checkh(u_mid.u_cam.WIDTH, 32'd8);
    `checkh(u_mid.u_depth.WIDTH, 32'd9);
    `checkh(u_mid.u_q.WIDTH, 32'd110);
    `checkh(u_ph.tag_val, 8'd11);
    `checkh(u_ph.cam_val, 8'd7);
    // (6) $bits(wrap_t) = 8 (payload) + 1 (v) = 9
    `checkh($bits(u_mid.u_sink.data), 32'd9);
    // (7) localparam type widths
    `checkh($bits(t_plain), 32'd12);
    `checkh($bits(t_alias), 32'd9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
