// DESCRIPTION: Verilator: Verilog Test module
//
// Chained class scope resolution in *type* position: `pkg::cls::t` and
// `pkg::cls#(P)::t`.
//
// V3LinkDot's visit(AstRefDType) resolves the scope operand, but only handled a
// single AstClassOrPackageRef.  With two '::' the operand is an AstDot holding a
// ref per scope, which fell to an E_UNSUPPORTED ("Multiple '::' package/class
// reference") followed by "Can't find typedef".  Value position (`pkg::cls::n`
// in a localparam) already worked -- only the type path was missing.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package P;
  class Plain;
    typedef logic [7:0] t;
    localparam int n = 8;
  endclass

  class Par #(
      parameter int W = 8
  );
    typedef logic [W-1:0] t;
    localparam int n = W;
  endclass

  class Outer;
    class Inner;
      typedef logic [6:0] t;
    endclass
  endclass

  // Traits-class shape: types derived from a struct config parameter
  typedef struct packed {
    int depth;
    int counters;
  } config_t;

  virtual class cfg #(
      parameter config_t c
  );
    localparam int width = $clog2(c.depth);
    localparam int counters = c.counters;
    typedef logic [width-1:0] data_t;
  endclass
endpackage

// Class-scoped types crossing a module boundary, as a port and inside a
// packed struct alongside type-parameter members.
module Sub #(
    parameter P::config_t cfg,
    parameter type        stk_t = logic
) (
    input  P::cfg#(cfg)::data_t                 din,
    input  logic [P::cfg#(cfg)::counters-1:0]   mask,
    input  stk_t                                stk,
    output P::cfg#(cfg)::data_t                 dout
);
  typedef struct packed {
    P::cfg#(cfg)::data_t d;
    stk_t                s;
  } packed_t;
  packed_t p;
  always_comb p = '{d: din, s: stk};
  always_comb dout = p.d;
  initial begin
    `checkh($bits(din), 12);
    `checkh($bits(mask), 4);
  end
endmodule

module t;
  // (1) pkg::cls::type -- no parameters
  P::Plain::t a;
  // (2) pkg::cls#(P)::type -- parameterized
  P::Par#(12)::t b;
  // (3) through a typedef
  typedef P::Par#(5)::t c_t;
  c_t c;
  // (4) an arbitrarily deep class scope
  P::Outer::Inner::t d;
  // (5) value position (already worked; guards against regressing it)
  localparam int na = P::Plain::n;
  localparam int nb = P::Par#(12)::n;

  localparam P::config_t CFG = '{depth: 4096, counters: 4};
  typedef struct packed { logic [7:0] hi; } stk_t;
  P::cfg#(CFG)::data_t din, dout;

  Sub #(.cfg(CFG), .stk_t(stk_t)) sub (
      .din  (din),
      .mask ('0),
      .stk  ('0),
      .dout (dout)
  );

  initial begin
    a = '0;
    b = '0;
    c = '0;
    d = '0;
    din = '0;
    `checkh($bits(a), 8);
    `checkh($bits(b), 12);
    `checkh($bits(c), 5);
    `checkh($bits(d), 7);
    `checkh($bits(dout), 12);
    `checkh(na, 32'd8);
    `checkh(nb, 32'd12);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
