// DESCRIPTION: Verilator: Verilog Test module
//
// A hierarchical block whose cells reach outside it for a shared signal. The
// references are promoted to ports automatically; without that the child
// Verilation cannot resolve them, because it compiles the block with itself
// as top and the upper modules are pruned.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef logic [7:0] phi_t;

module tech(input phi_t phi, input en,
            input [3:0] pub /*verilator public_flat_rd*/);
endmodule

module leaf(output reg o, input i);
  // Reaches up and out of the enclosing hierarchical block
  // Typedef'd target: a name for a packed basic type is still promotable
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  wire       en = t.top.drv.tech_inst.en;
  // Target exposed to VPI; promotion must not disturb that
  wire [3:0] pb = t.top.drv.tech_inst.pub;
  // Bit select directly on the reference: the select binds to the last
  // identifier inside the dotted chain, and must survive promotion
  wire       b2 = t.top.drv.tech_inst.phi[2];
  always @(ph or i or en or b2 or pb) o <= en ? (i ^ ph[3] ^ b2 ^ pb[0]) : 1'b0;
endmodule

module blk(output o, input i);
  /*verilator hier_block*/
  leaf l0(o, i);
endmodule

module drv(output phi_t ph, output reg en, output reg [3:0] pub);
  tech tech_inst(ph, en, pub);
  assign ph = 8'h5a;
  initial begin en = 1'b1; pub = 4'ha; end
endmodule

module bench(output o, input i);
  phi_t ph;
  wire  en;
  wire [3:0] pub;
  drv drv(ph, en, pub);
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
