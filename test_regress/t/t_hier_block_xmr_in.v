// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// References into a hierarchical block, promoted to outputs on it. The block
// already has the signal, so nothing inside it is rewritten: the port is
// driven from the signal and the outside reads the port. Every value is
// checked in t_hier_block_xmr_in.cpp once the network has settled.

module deep(output [7:0] o);
  wire [7:0] sig = 8'h5a;
  wire signed [7:0] sgn = -8'sd5;
  typedef logic [7:0] byte_t;
  byte_t tdef = 8'h3c;
  assign o = sig;
endmodule

module mid(output [7:0] o);
  deep d(o);
endmodule

// The reference reaches three levels in, not just to the block's own top
module blk(output [7:0] o);
  /*verilator hier_block*/
  mid m(o);
endmodule

// A de-parameterized block, whose mangled name the ports must still follow
module blk_param #(parameter int P = 1) (output [7:0] o);
  /*verilator hier_block*/
  mid m(o);
endmodule

module bench(output [7:0] o_blk, output [7:0] o_param,
             output [7:0] o_sig, output [7:0] o_again, output o_bit,
             output [3:0] o_part, output o_neg, output [7:0] o_tdef);
  blk bk(o_blk);
  blk_param #(.P(2)) bp(o_param);
  assign o_sig = bk.m.d.sig;        // three levels inside the block
  assign o_again = bk.m.d.sig;      // the same path again: one port, read twice
  assign o_bit = bk.m.d.sig[1];     // a bit select is kept, re-based on the port
  assign o_part = bk.m.d.sig[7:4];  // and so is a part select
  assign o_neg = (bk.m.d.sgn < 0);  // a signed target must stay signed
  assign o_tdef = bk.m.d.tdef;      // a typedef'd target is still promotable
endmodule

module t(output [7:0] o_blk, output [7:0] o_param,
         output [7:0] o_sig, output [7:0] o_again, output o_bit,
         output [3:0] o_part, output o_neg, output [7:0] o_tdef,
         output [7:0] o_above);
  bench top(o_blk, o_param, o_sig, o_again, o_bit, o_part, o_neg, o_tdef);
  // Reached from two levels above the block, not from its parent
  assign o_above = top.bk.m.d.sig;
endmodule
