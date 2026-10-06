// DESCRIPTION: Verilator: Verilog Test module
//
// Shapes the single-instance tests do not reach: one block instanced twice so
// two instances share a promoted port, a block whose parent is not the top,
// and a reference made from inside a generate block.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tech(input [7:0] phi);
endmodule

// Reference made from inside a generate block, not at module level
module leaf(output [1:0] o, input i);
  generate
    for (genvar gi = 0; gi < 2; ++gi) begin : g
      wire [7:0] ph = t.top.drv.tech_inst.phi;
      assign o[gi] = i ^ ph[gi];
    end
  endgenerate
endmodule

module blk(output [1:0] o, input i);
  /*verilator hier_block*/
  leaf l0(o, i);
endmodule

// The block's parent is this, not the top
module mid(output [3:0] o, input i);
  blk a(o[1:0], i);
  blk b(o[3:2], i);
endmodule

module drv(output [7:0] ph);
  tech tech_inst(ph);
  assign ph = 8'h5a;
endmodule

module bench(output [3:0] o, input i);
  wire [7:0] ph;
  drv drv(ph);
  mid m(o, i);
endmodule

module t(output [3:0] o_bits);
  reg i = 1'b0;
  bench top(o_bits, i);
endmodule
