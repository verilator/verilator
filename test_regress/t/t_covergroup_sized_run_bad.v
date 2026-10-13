// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Arrays of bins, and crosses of them, whose sizes are known when the covergroup is constructed

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [3:0] value;
  bit [15:0] data;
  bit [63:0] data64;

  covergroup cg_count(int count);
    cp: coverpoint value {
      bins b[count] = {[0 : 3]};  // <--- Bad: count
    }
  endgroup

  covergroup cg_limit(int count);
    cp: coverpoint data {
      bins b[count] = {[0 : $]};  // <--- Bad: count
    }
  endgroup

  // Four dimensions of 1024 bins exceed the 2^32-1 bins of a cross
  covergroup cg_cross(int count);
    c1: coverpoint data {
      bins b[count] = {[0 : $]};
    }
    c2: coverpoint data {
      bins b[count] = {[0 : $]};
    }
    c3: coverpoint data {
      bins b[count] = {[0 : $]};
    }
    c4: coverpoint data {
      bins b[count] = {[0 : $]};
    }
    xx: cross c1, c2, c3, c4;  // <--- Bad: bins
  endgroup

  // All 2^64 values, whose positions need more than 64 bits
  covergroup cg_full;
    cp: coverpoint data64 {
      bins b[2] = {[0 : $]};
    }
  endgroup

  cg_count zero;
  cg_count negative;
  cg_count valid;
  cg_limit over_limit;
  cg_cross oversized;
  cg_full full;

  initial begin
    // Not a positive size (IEEE 1800-2023 19.5.1), so an error, and the array has no bins
    zero = new(0);
    negative = new(-1);
    zero.sample();
    `checkr(zero.get_inst_coverage(), 0.0);
    zero = null;
    negative = null;

    // More bins than --coverage-max-bins hold values, so the array is ignored
    over_limit = new(2000);
    over_limit.sample();
    `checkr(over_limit.get_inst_coverage(), 0.0);

    // The cross is ignored, but not its coverpoints
    oversized = new(1024);
    oversized.sample();
    `checkr(oversized.get_inst_coverage(), 100.0 / 1024);
    oversized = null;

    valid = new(2);
    for (int i = 0; i < 4; ++i) begin
      value = 4'(i);
      valid.sample();
    end
    `checkr(valid.get_inst_coverage(), 100.0);

    full = new;
    data64 = 64'hffff_ffff_ffff_ffff;
    full.sample();
    `checkr(full.get_inst_coverage(), 50.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
