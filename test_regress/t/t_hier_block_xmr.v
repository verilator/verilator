// DESCRIPTION: Verilator: Verilog Test module
//
// A hierarchical block whose cells reach outside it for a shared signal. The
// references are promoted to ports automatically; without that the child
// Verilation cannot resolve them, because it compiles the block with itself
// as top and the upper modules are pruned.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tech(input [7:0] phi, input en);
endmodule

module leaf(output reg o, input i);
  // Reaches up and out of the enclosing hierarchical block
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  wire       en = t.top.drv.tech_inst.en;
  // Bit select directly on the reference: the select binds to the last
  // identifier inside the dotted chain, and must survive promotion
  wire       b2 = t.top.drv.tech_inst.phi[2];
  always @(ph or i or en or b2) o <= en ? (i ^ ph[3] ^ b2) : 1'b0;
endmodule

module blk(output o, input i);
  /*verilator hier_block*/
  leaf l0(o, i);
endmodule

module drv(output reg [7:0] ph, output reg en);
  tech tech_inst(ph, en);
  initial begin ph = 8'h5a; en = 1'b1; end
endmodule

module bench(output o, input i);
  wire [7:0] ph;
  wire       en;
  drv drv(ph, en);
  blk b(o, i);
endmodule

module t;
  wire o;
  reg  i = 1'b1;
  bench top(o, i);

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
