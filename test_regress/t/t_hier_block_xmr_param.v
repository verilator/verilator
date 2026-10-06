// DESCRIPTION: Verilator: Verilog Test module
//
// A parameterized hierarchical block whose cells reach outside it. The block is
// de-parameterized to a mangled name, which the promoted ports must follow.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tech(input [7:0] phi);
endmodule

module leaf #(parameter int SEL = 0) (output reg o, input i);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  always @(ph or i) o <= i ^ ph[SEL];
endmodule

module blk #(parameter int P = 3) (output o, input i);
  /*verilator hier_block*/
  leaf #(.SEL(P)) l0(o, i);
endmodule

module drv(output [7:0] ph);
  tech tech_inst(ph);
  assign ph = 8'h5a;
endmodule

module bench(output o, input i);
  wire [7:0] ph;
  drv drv(ph);
  blk #(.P(2)) b(o, i);
endmodule

// Checked from C++ once the network has settled: o is i ^ ph[SEL], and with
// SEL parameterized to 2 that reads 0x5a bit 2, which is 0.
module t(output o_bit);
  reg i = 1'b1;
  bench top(o_bit, i);
endmodule
