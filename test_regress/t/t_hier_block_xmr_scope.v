// DESCRIPTION: Verilator: Verilog Test module
//
// A dotted path is relative to the module it appears in. Two modules in the
// same hierarchical block spell the same path, but only one of them reaches
// outside; the other resolves to its own instance and must be left alone.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tech(input [7:0] phi);
endmodule

// Reaches outside: this one must be promoted
// 0x5a[1] is 1; the inner source has 0 there, so a wrong rewrite shows up
module leaf_out(output reg o, input i);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  always @(ph or i) o <= i ^ ph[1];
endmodule

// Has its OWN internal instance spelled the same way; must NOT be promoted
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
module leaf_in(output reg o, input i);
  wire [7:0] lcl;
  t_local t(lcl);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  // 0x3c[2] is 1, 0x5a[2] is 0: promoting this reference flips the answer
  always @(ph or i) o <= i ^ ph[2];
endmodule

module blk(output [1:0] o, input i);
  /*verilator hier_block*/
  wire o1, o2;
  leaf_out a(o1, i);
  leaf_in  b(o2, i);
  assign o = {o2, o1};
endmodule

module drv(output [7:0] ph);
  tech tech_inst(ph);
  assign ph = 8'h5a;
endmodule

module bench(output [1:0] o, input i);
  wire [7:0] ph;
  drv drv(ph);
  blk b(o, i);
endmodule

// o[0] is leaf_out's, o[1] leaf_in's; checked from C++ once the network has
// settled, which an initial block here would run too early to do.
module t(output [1:0] o_bits);
  reg i = 1'b0;
  bench top(o_bits, i);
endmodule
