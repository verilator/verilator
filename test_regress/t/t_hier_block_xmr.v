// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// References out of a hierarchical block, promoted to ports on it. Each block
// below is a shape the promotion has to get right, and every output is checked
// in t_hier_block_xmr.cpp once the combinational network has settled.

package cfg_pkg;
  localparam int SEL = 3;
endpackage

typedef logic [7:0] phi_t;

module tech(input phi_t phi, input en,
            input [3:0] pub /*verilator public_flat_rd*/,
            input signed [7:0] sgn);
endmodule

// --- The target forms -------------------------------------------------------
module leaf(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit,
            output [3:0] o_part);
  // Typedef'd target: a name for a packed basic type is still promotable
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  wire       en = t.top.drv.tech_inst.en;
  // Target exposed to VPI; promotion must not disturb that
  wire [3:0] pb = t.top.drv.tech_inst.pub;
  // Signed target: the promoted port must stay signed
  wire signed [7:0] sg = t.top.drv.tech_inst.sgn;
  // Bit select binds to the last identifier inside the chain
  wire       b2 = t.top.drv.tech_inst.phi[2];
  // A part select must be kept and re-based on the promoted port too
  wire [3:0] pt = t.top.drv.tech_inst.phi[7:4];
  // A package-scoped name is not a hierarchical reference and must not match
  wire       px = ph[cfg_pkg::SEL];

  assign o_ph = ph;
  assign o_en = en;
  assign o_pub = pb;
  assign o_neg = (sg < 0);
  assign o_bit = b2 ^ px;
  assign o_part = pt;
endmodule

// Reads the same path as leaf; both must share one generated port
module leaf2(output [7:0] o_ph2);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  assign o_ph2 = ph;
endmodule

module blk(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit,
           output [3:0] o_part, output [7:0] o_ph2);
  /*verilator hier_block*/
  leaf  l0(o_ph, o_en, o_pub, o_neg, o_bit, o_part);
  leaf2 l1(o_ph2);
endmodule

// --- Scoping: the same path means different things in different modules ------
// Reaches outside: 0x5a[1] is 1, and the inner source has 0 there
module leaf_out(output reg o, input i);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  always @(ph or i) o <= i ^ ph[1];
endmodule

module inner_tech(output [7:0] phi);
  assign phi = 8'h3c;
endmodule
module drv_local(output [7:0] out);
  inner_tech tech_inst(out);
endmodule
module top_local(output [7:0] out);
  drv_local drv(out);
endmodule
module t_local(output [7:0] out);
  top_local top(out);
endmodule

// Spells the same path at its own instance; must not be promoted. 0x3c[2] is
// 1 where 0x5a[2] is 0, so a wrong rewrite flips the answer.
module leaf_in(output reg o, input i);
  wire [7:0] lcl;
  t_local t(lcl);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  always @(ph or i) o <= i ^ ph[2];
endmodule

module blk_scope(output [1:0] o, input i);
  /*verilator hier_block*/
  wire o1, o2;
  leaf_out a(o1, i);
  leaf_in  b(o2, i);
  assign o = {o2, o1};
endmodule

// --- A de-parameterized block, whose mangled name the ports must follow ------
module leaf_param #(parameter int SEL = 0) (output reg o, input i);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  always @(ph or i) o <= i ^ ph[SEL];
endmodule

module blk_param #(parameter int P = 3) (output o, input i);
  /*verilator hier_block*/
  leaf_param #(.SEL(P)) l0(o, i);
endmodule

// --- Two instances sharing a port, below a parent that is not the top -------
// The reference is made inside a generate block, not at module level
module leaf_gen(output [1:0] o, input i);
  generate
    for (genvar gi = 0; gi < 2; ++gi) begin : g
      wire [7:0] ph = t.top.drv.tech_inst.phi;
      assign o[gi] = i ^ ph[gi];
    end
  endgenerate
endmodule

module blk_gen(output [1:0] o, input i);
  /*verilator hier_block*/
  leaf_gen l0(o, i);
endmodule

module mid(output [3:0] o, input i);
  blk_gen a(o[1:0], i);
  blk_gen b(o[3:2], i);
endmodule

// --- The design under all of the above --------------------------------------
module drv(output phi_t ph, output en, output [3:0] pub, output signed [7:0] sgn);
  tech tech_inst(ph, en, pub, sgn);
  assign ph = 8'h5a;
  assign en = 1'b1;
  assign pub = 4'ha;
  assign sgn = -8'sd5;
endmodule

module bench(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit,
             output [3:0] o_part, output [7:0] o_ph2, output [1:0] o_scope, output o_param,
             output [3:0] o_gen, input i_zero, input i_one);
  phi_t ph;
  wire  en;
  wire [3:0] pub;
  wire signed [7:0] sgn;
  drv drv(ph, en, pub, sgn);
  blk       b(o_ph, o_en, o_pub, o_neg, o_bit, o_part, o_ph2);
  blk_scope s(o_scope, i_zero);
  blk_param #(.P(2)) p(o_param, i_one);
  mid       m(o_gen, i_zero);
endmodule

module t(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit,
         output [3:0] o_part, output [7:0] o_ph2, output [1:0] o_scope, output o_param,
         output [3:0] o_gen);
  reg i_zero = 1'b0;
  reg i_one = 1'b1;
  bench top(o_ph, o_en, o_pub, o_neg, o_bit, o_part, o_ph2, o_scope, o_param, o_gen,
            i_zero, i_one);
endmodule
