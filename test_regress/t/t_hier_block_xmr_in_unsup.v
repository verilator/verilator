// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// References into a hierarchical block that cannot be promoted to a port.
// Each must be refused rather than silently mis-modelled, since a wrong width
// or a dropped write is wrong hardware.

module inner #(parameter int W = 8) (output [7:0] o);
  parameter CONSTVAL = 3;
  wire [W-1:0] parm = 8'h5a;        // width is parameterized
  real         anal = 1.0;          // non-integral
  wire [7:0]   sig = 8'h5a;
  reg          flag;
  reg [7:0]    xmrport_0;           // collides with the generated name
  assign o = sig;
endmodule

module blk(output [7:0] o);
  /*verilator hier_block*/
  inner i0(o);
  generate
    for (genvar gi = 0; gi < 2; ++gi) begin : gen
      inner g_in(o);
    end
  endgenerate
endmodule

module bench(output [7:0] o, output [7:0] a, output b, output c,
             output [7:0] d, output e, output [7:0] f);
  blk bk(o);
  // 1. Width is parameterized, so not knowable before elaboration
  assign a = bk.i0.parm;
  // 2. Non-integral type
  assign b = (bk.i0.anal > 0.0);
  // 3. Writing a signal inside the block
  assign bk.i0.flag = 1'b1;
  // 4. Target is a parameter: a port would make a constant a runtime value
  assign c = bk.i0.CONSTVAL[0];
  // 5. Path indexes a scope, which the rewrite cannot spell back
  assign d = bk.gen[1].g_in.sig;
  // 6. Generated port name collides with a signal the block already declares
  assign f = bk.i0.xmrport_0;
  assign e = 1'b0;
endmodule

module t(output [7:0] o, output [7:0] a, output b, output c,
         output [7:0] d, output e, output [7:0] f);
  bench top(o, a, b, c, d, e, f);
endmodule
