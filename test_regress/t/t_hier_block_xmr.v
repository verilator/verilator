// DESCRIPTION: Verilator: Verilog Test module
//
// A hierarchical block whose cells reach outside it for shared signals. The
// references are promoted to ports automatically; without that the child
// Verilation cannot resolve them, because it compiles the block with itself
// as top and the upper modules are pruned.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package cfg_pkg;
  localparam int SEL = 3;
endpackage

typedef logic [7:0] phi_t;

module tech(input phi_t phi, input en,
            input [3:0] pub /*verilator public_flat_rd*/,
            input signed [7:0] sgn);
endmodule

module leaf(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit);
  // Typedef'd target: a name for a packed basic type is still promotable
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  wire       en = t.top.drv.tech_inst.en;
  // Target exposed to VPI; promotion must not disturb that
  wire [3:0] pb = t.top.drv.tech_inst.pub;
  // Signed target: the promoted port must stay signed
  wire signed [7:0] sg = t.top.drv.tech_inst.sgn;
  // Bit select binds to the last identifier inside the chain
  wire       b2 = t.top.drv.tech_inst.phi[2];
  // A package-scoped name is not a hierarchical reference and must not match
  wire       px = ph[cfg_pkg::SEL];

  assign o_ph = ph;
  assign o_en = en;
  assign o_pub = pb;
  assign o_neg = (sg < 0);
  assign o_bit = b2 ^ px;
endmodule

module blk(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit);
  /*verilator hier_block*/
  leaf l0(o_ph, o_en, o_pub, o_neg, o_bit);
endmodule

module drv(output phi_t ph, output en, output [3:0] pub, output signed [7:0] sgn);
  tech tech_inst(ph, en, pub, sgn);
  assign ph = 8'h5a;
  assign en = 1'b1;
  assign pub = 4'ha;
  assign sgn = -8'sd5;
endmodule

module bench(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit);
  phi_t ph;
  wire  en;
  wire [3:0] pub;
  wire signed [7:0] sgn;
  drv drv(ph, en, pub, sgn);
  blk b(o_ph, o_en, o_pub, o_neg, o_bit);
endmodule

module t(output [7:0] o_ph, output o_en, output [3:0] o_pub, output o_neg, output o_bit);
  bench top(o_ph, o_en, o_pub, o_neg, o_bit);
endmodule
