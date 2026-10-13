// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A cross bin 'with' filter is evaluated for the value tuples of each choice of bins of the cross
// items it reads, at most 2**32 when the covergroup is constructed

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [32:0] v33;
  bit [15:0] v16a;
  bit [15:0] v16b;
  bit [63:0] v64;
  bit [5:0] v6;
  bit [1024:0] v1025;
  bit flag;
  real r;

  covergroup cg;
    big: coverpoint v33 {
      option.weight = 0;
      bins all = {[0 : 33'h1_ffff_ffff]};
    }
    halves: coverpoint v33 {
      option.weight = 0;
      bins low = {[0 : 33'h0_8000_0000]};
      bins high = {[33'h1_0000_0000 : 33'h1_8000_0000]};
    }
    aa: coverpoint v16a {
      option.weight = 0;
      bins all = {[0 : 16'hffff]};
    }
    bb: coverpoint v16b {
      option.weight = 0;
      bins all = {[0 : 16'hffff]};
    }
    sparse: coverpoint v64 {
      option.weight = 0;
      wildcard bins ends = {64'h?000_0000_0000_000?};  // 2**8 values over about 2**64
    }
    each: coverpoint v6 {
      option.weight = 0;
      bins v[] = {[0 : 63]};
    }
    // Wider than the exclusion analysis's depth limit, so 'pair' is retained, of excluded values
    deep: coverpoint v1025 {
      option.weight = 0;
      bins pair = {[0 : 1]};
      bins rest = {[2 : $]};
      ignore_bins both = {[0 : 1]};
    }
    ff: coverpoint flag {option.weight = 0;}
    rr: coverpoint r {
      option.weight = 0;
      bins zero = {[0.0 : 0.5]};
      bins one = {[1.0 : 1.5]};
    }
    x_big: cross big, ff{
      bins over = x_big with (big == 1);  // <--- Bad: 2**33 value tuples
      bins unread = x_big with (ff == 1);  // Of 'ff' only: <all,auto[1]>
    }
    x_sum: cross halves, ff{
      bins over = x_sum with (halves == 0);  // <--- Bad: 2 * (2**31 + 1) value tuples
    }
    x_product: cross aa, bb{
      bins limit = x_product with (aa == 0 && bb == 0);  // 2**32 value tuples, the first true
    }
    x_sparse: cross sparse, ff{
      bins ends = x_sparse with (sparse != 0);  // 2**8 value tuples
    }
    // A bin of an unsupported selection has no code, so its filter does not ignore the next bin
    x_unsup: cross big, rr{
      // verilator lint_off COVERIGN
      bins unsup = (x_unsup with (big == 1)) || (x_unsup with (rr == 0.0));
      // verilator lint_on COVERIGN
      ignore_bins one = binsof (rr.one);  // <all,one>
    }
    // Of 128 bin tuples, in two words, the first without a tuple to filter
    x_words: cross each, ff{
      // <v[63],auto[1]>
      ignore_bins top = binsof (each) intersect {[32 : 63]} with (each + ff == 64);
    }
    x_deep: cross deep, halves{
      bins none = binsof (deep.pair) with (deep == 0);  // Of no value tuple
      bins over = binsof (deep.rest) with (deep != 1025'(halves));  // <--- Bad: ~2**1056 tuples
    }
  endgroup

  // A cross item has the type of its coverpoint's expression, whose names, in nested scopes too,
  // are outside the filter, where the cross items hide them
  logic [1:0] a;
  int offset = 16;
  bit one[1] = '{1};

  covergroup cg_scope;
    offset: coverpoint a;
    // Of the module's 'offset', in the scope of the array method's 'with': 32 bits wide
    total: coverpoint (one.sum() with (item + offset)) {bins values = {17};}
    xx: cross offset, total{
      bins wide = xx with ($bits(total) == 32);  // All 4 bin tuples
    }
  endgroup

  cg inst = new;
  cg_scope scope_inst = new;

  initial begin
    v33 = 1;
    v16a = 1;
    v16b = 1;
    v64 = 1;
    v6 = 63;
    v1025 = 2;
    flag = 1;
    inst.sample();
    scope_inst.sample();
    // x_big: unread of 2 bins; x_sum: one of 4 automatic bins; x_product: limit of 1 bin;
    // x_sparse: ends of 1 bin; x_unsup: <all,zero> of 1 automatic bin; x_words: none of 127
    // automatic bins; x_deep: <rest,low> of 4 automatic bins
    `checkr(inst.get_inst_coverage(),
            (50.0 + 25.0 + 100.0 + 100.0 + 100.0 + 0.0 + 25.0) / 7.0);
    // offset: 1 of 4 bins; total: 1 of 1; xx: 'wide' of 1, not 1 of 4 automatic bins
    `checkr(scope_inst.get_inst_coverage(), (25.0 + 100.0 + 100.0) / 3.0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
