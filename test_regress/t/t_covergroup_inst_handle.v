// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Design half of the VlCovInstHandle test.  All this has to do is create a
// covergroup instance and never let go of it, so that the registry still has an
// attached node when the C++ harness destroys the context.
//
// See t_covergroup_inst_handle.cpp for what is actually being tested.

module t (
    input clk
);

  int cyc = 0;
  logic [1:0] v;

  covergroup cg_ctx;
    cp: coverpoint v {
      bins b0 = {0};
      bins b1 = {1};
    }
  endgroup

  cg_ctx g;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      g = new;
      v = 0;
      g.sample();
    end else if (g == null) begin
      // Never taken.  It exists to *read* g: a covergroup handle that is written
      // and never read is localized into this block, and the instance would then
      // be dropped at the end of the edge that created it -- leaving nothing
      // attached, and this test measuring nothing.
      $stop;
    end
  end
endmodule
