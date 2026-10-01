// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Wildcard arrays of bins of more values, or ranges of values, than --coverage-max-bins 4.  An
// ignore or illegal array still excludes or checks all its values, as one bin, and an ignored
// array leaves its coverpoint without bins, rather than automatic ones (IEEE 1800-2023 19.11.1).
// Bins filtering as many ranges of values with 'with' are ignored, excluding no values.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [3:0] v;
  bit [3:0] x;
  int illegal;
  bit [1:0] t;

  covergroup cg;
    // The odd values are excluded, so 'all' holds the even ones
    ign: coverpoint v {
      bins all = {[0 : 15]};
      wildcard ignore_bins odd[] = {4'b???1};
    }
    ign_sized: coverpoint v {
      bins all = {[0 : 15]};
      wildcard ignore_bins odd[2] = {4'b???1};
    }
    // Values 8..15, and the odd values, are illegal
    ill: coverpoint x {
      bins all = {[0 : 15]};
      wildcard illegal_bins high[] = {4'b1???};
    }
    ill_sized: coverpoint x {
      bins all = {[0 : 15]};
      wildcard illegal_bins odd[2] = {4'b???1};
    }
    only: coverpoint v {
      wildcard bins odd[2] = {4'b???1};
    }
    with_only: coverpoint v {
      wildcard bins odd[] = {4'b???1} with (1);
    }
    with_ign: coverpoint v {
      bins all = {[0 : 15]};
      wildcard ignore_bins odd = {4'b???1} with (item > 1);
    }
    // A cross selects the bins ignored as no bins, which it then does not have
    mixed: coverpoint v {
      bins low = {[0 : 3]};
      wildcard bins odd[] = {4'b???1} with (item > 8);
      wildcard bins odd_sized[2] = {4'b???1};
      bins many[] = {[0 : 15]};
    }
    ct: coverpoint t;
    xm: cross mixed, ct{
      bins sel_odd = binsof (mixed.odd);
      bins sel_sized = binsof (mixed.odd_sized);
      bins sel_many = binsof (mixed.many);
      bins sel_low = binsof (mixed.low);
    }
  endgroup

  cg cg_inst = new;

  initial begin
    for (int i = 0; i < 16; ++i) begin
      v = 4'(i);
      x = 4'(i % 4 * 2);
      t = 2'(i);
      cg_inst.sample();
    end
    // All of the coverpoints with bins, which 'only' and 'with_only' are not
    `checkr(cg_inst.get_inst_coverage(), 100.0);
    if ($value$plusargs("illegal=%d", illegal)) begin
      x = 4'(illegal);
      cg_inst.sample();
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
