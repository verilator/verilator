// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Wildcard arrays of bins of more values, or ranges of values, than --coverage-max-bins 4.  An
// ignore or illegal array still excludes or checks all its values, as one bin, and an ignored
// array leaves its coverpoint without bins, rather than automatic ones (IEEE 1800-2023 19.11.1).

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [3:0] v;
  bit [3:0] x;
  int illegal;

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
  endgroup

  cg cg_inst = new;

  initial begin
    for (int i = 0; i < 16; ++i) begin
      v = 4'(i);
      x = 4'(i % 4 * 2);
      cg_inst.sample();
    end
    // All of the coverpoints with bins, which 'only' is not
    `checkr(cg_inst.get_inst_coverage(), 100.0);
    if ($value$plusargs("illegal=%d", illegal)) begin
      x = 4'(illegal);
      cg_inst.sample();
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
