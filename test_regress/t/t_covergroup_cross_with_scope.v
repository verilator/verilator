// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// The candidate value of a cross item has the type of its coverpoint's expression, whose names,
// in nested scopes too, are outside the 'with' filter, where the cross items hide them

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [1:0] a;
  int offset = 16;
  bit one[1] = '{1};

  covergroup cg;
    offset: coverpoint a;
    // Of the module's 'offset', in the scope of the array method's 'with': 32 bits wide
    total: coverpoint (one.sum() with (item + offset)) {bins values = {17};}
    xx: cross offset, total{
      bins wide = xx with ($bits(total) == 32);  // All 4 bin tuples
    }
  endgroup

  cg inst = new;

  initial begin
    a = 0;
    inst.sample();
    // offset: 1 of 4 bins; total: 1 of 1; xx: 'wide' of 1, not 1 of 4 automatic bins
    `checkr(inst.get_inst_coverage(), (25.0 + 100.0 + 100.0) / 3.0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
