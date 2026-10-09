// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Sized arrays of bins, 'bins b[N] = {...}' (IEEE 1800-2023 19.5.1)

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`define SIZED_BASE 3

module t;
  bit [3:0] v;
  bit signed [4:0] s;
  bit [63:0] q;
  bit [99:0] w;
  bit en;
  localparam DOLLAR = $;

  function automatic int twice(int n);
    return 2 * n;
  endfunction

  // The examples of IEEE 1800-2023 19.5.1
  covergroup cg_ieee;
    // 13 values over 4 bins of 3, the last holding the rest: <1,2,3>, <4,5,6>, <7,8,9>,
    // <10,1,4,7>
    fixed4: coverpoint v {
      bins fixed[4] = {[1 : 10], 1, 4, 7};
    }
    // More bins than values: <1>, <4>, <7>, and two empty bins, which are not created
    fixed5: coverpoint v {
      bins fixed[5] = {1, 4, 7};
    }
  endgroup

  // Values distribute in the coverpoint's order, and count once in each bin holding them
  covergroup cg_values;
    // -16..15 over 3 bins of 10, the last holding 12
    sgn: coverpoint s {
      bins b[3] = {[$ : $]};
    }
    // A value two elements put in one bin
    rep: coverpoint v {
      bins b[1] = {[1 : 3], 2};
    }
    // Values two elements put in two bins: <1,2,3>, <2,3,7>
    dup: coverpoint v {
      bins b[2] = {[1 : 3], 2, 3, 7};
    }
    // All 2^64 values of a 64-bit coverpoint, in bins of 2^62
    full: coverpoint q {
      bins b[4] = {[0 : $]};
    }
    // 2^100 values, the last bin holding the rest
    wide: coverpoint w {
      bins b[3] = {[0 : $]};
    }
  endgroup

  // Counts and bounds given to the constructor
  covergroup cg_dynamic(int lo, int hi, longint unsigned count);
    cp: coverpoint v {
      bins b[count] = {[lo : hi]};
    }
  endgroup

  // Counts and bounds of other types
  covergroup cg_types(
      bit [2:0] count, bit [69:0] wide_count, byte lo, bit signed [4:0] slo, bit [99:0] wlo
  );
    // An unsigned count, and the values from lo to the last coverpoint value
    open: coverpoint v {
      bins b[count] = {[lo : $]};
    }
    // A count beyond 64 bits
    many: coverpoint v {
      bins b[wide_count] = {[0 : 3]};
    }
    // A bound of the signed coverpoint's type
    sgn: coverpoint s {
      bins b[2] = {[slo : 3]};
    }
    // A bound beyond 64 bits
    wide: coverpoint w {
      bins b[count] = {[wlo : $]};
    }
  endgroup

  // Sizes of expressions of constants, constructor arguments, and functions (IEEE 1800-2023
  // 19.5)
  covergroup cg_exprs(int n);
    // A macro and an argument: 4 bins of 4
    macro_arg: coverpoint v {
      bins b[`SIZED_BASE + n] = {[0 : 15]};
    }
    // A function of an argument: 2 bins of 8
    func_arg: coverpoint v {
      bins b[twice(n)] = {[0 : 15]};
    }
    // A constant system function, not '$': 4 bins of 4
    sys_func: coverpoint v {
      bins b[$clog2(16)] = {[0 : 15]};
    }
    // A parameter of '$' bounding a range (IEEE 1800-2023 6.20.7): 0..5 in 2 bins of 3
    param_dollar: coverpoint v {
      bins b[2] = {[DOLLAR : 5]};
    }
  endgroup

  // An embedded covergroup sized by a member of its enclosing class
  class Sized;
    const int m_count;
    bit [3:0] m_value;
    covergroup cg_embedded;
      cp: coverpoint m_value {
        bins b[m_count] = {[0 : 15]};
      }
    endgroup
    function new(int count);
      m_count = count;
      cg_embedded = new;
    endfunction
  endclass

  // Other bins of a coverpoint, other kinds of sized arrays, and crosses
  covergroup cg_kinds;
    // The default bin holds the values no bin holds, 6..15
    dflt: coverpoint v {
      bins b[2] = {[0 : 5]};
      bins others = default;
    }
    // Excluded values leave bins: <0,1,2> of b loses them all, and is removed
    excl: coverpoint v {
      bins b[3] = {[0 : 8]};
      ignore_bins ign[2] = {[0 : 2], 5};
      illegal_bins ill[2] = {14, 15};
    }
    gated: coverpoint v {
      bins b[2] = {[0 : 3]} iff (en);
    }
    // A sized array's bins follow the others: <8,9>, <10,11>
    mixed: coverpoint v {
      bins sized[2] = {[8 : 11]};
      bins one = {0};
      bins arr[] = {[1 : 2]};
    }
    xx: cross dflt, gated{bins low = binsof (dflt.b) intersect {[0 : 2]};}
  endgroup

  cg_ieee ieee_inst = new;
  cg_values values_inst = new;
  cg_dynamic split_inst;
  cg_dynamic many_inst;
  cg_dynamic clip_inst;
  cg_dynamic none_inst;
  cg_types types_inst;
  cg_exprs exprs_inst;
  cg_kinds kinds_inst = new;
  Sized obj;

  initial begin
    v = 1;
    ieee_inst.sample();
    v = 10;
    ieee_inst.sample();
    v = 5;
    ieee_inst.sample();
    v = 7;
    ieee_inst.sample();
    // fixed4: all 4 bins, fixed5: 2 of 3 bins
    `checkr(ieee_inst.get_inst_coverage(), 100.0 * (1.0 + 2.0 / 3) / 2);

    s = -7;
    v = 2;
    q = 64'h3fff_ffff_ffff_ffff;
    w = 100'h0;
    values_inst.sample();
    s = -6;
    v = 7;
    q = 64'h4000_0000_0000_0000;
    w = {100{1'b1}};
    values_inst.sample();
    // sgn: b[0], b[1]; rep: b[0], once; dup: both; full: b[0], b[1]; wide: b[0], b[2]
    `checkr(values_inst.get_inst_coverage(), 100.0 * (2.0 / 3 + 1.0 + 1.0 + 2.0 / 4 + 2.0 / 3) / 5);

    // 6 values over 2 bins: <1,2,3>, <4,5,6>
    split_inst = new(1, 6, 2);
    v = 3;
    split_inst.sample();
    `checkr(split_inst.get_inst_coverage(), 50.0);
    v = 4;
    split_inst.sample();
    `checkr(split_inst.get_inst_coverage(), 100.0);
    // 8 values over more than 2^32 bins: 8 bins of one
    many_inst = new(0, 7, 64'h1_0000_0001);
    for (int i = 0; i < 3; ++i) begin
      v = 4'(i);
      many_inst.sample();
    end
    `checkr(many_inst.get_inst_coverage(), 100.0 * (3.0 / 8));
    // The values of -5..20 that are coverpoint values, 0..15, over 3 bins of 5 and 6
    clip_inst = new(-5, 20, 3);
    v = 15;
    clip_inst.sample();
    `checkr(clip_inst.get_inst_coverage(), 100.0 * (1.0 / 3));
    v = 9;
    clip_inst.sample();
    `checkr(clip_inst.get_inst_coverage(), 100.0 * (2.0 / 3));
    // No coverpoint value, so no bin
    none_inst = new(16, 20, 2);
    none_inst.sample();
    `checkr(none_inst.get_inst_coverage(), 0.0);

    // 0..15 of -3..$ over 2 bins of 8, 4 values over more than 2^64 bins, -4..3 over 2 bins
    // of 4, and 2^100 - 1 values over 2 bins
    types_inst = new(2, {70{1'b1}}, -3, -4, 100'h1);
    v = 9;
    s = -2;
    types_inst.sample();
    v = 1;
    types_inst.sample();
    // open: both bins; many: b[1] of 4; sgn: b[0] of 2; wide: b[1] of 2
    `checkr(types_inst.get_inst_coverage(), 100.0 * (1.0 + 1.0 / 4 + 1.0 / 2 + 1.0 / 2) / 4);

    // First and last bins: macro_arg 2 of 4, func_arg both, sys_func 2 of 4, param_dollar 1 of 2
    exprs_inst = new(1);
    v = 0;
    exprs_inst.sample();
    v = 15;
    exprs_inst.sample();
    `checkr(exprs_inst.get_inst_coverage(), 100.0 * (1.0 / 2 + 1.0 + 1.0 / 2 + 1.0 / 2) / 4);

    // 16 values over 4 bins of 4
    obj = new(4);
    obj.m_value = 5;
    obj.cg_embedded.sample();
    `checkr(obj.cg_embedded.get_inst_coverage(), 25.0);

    v = 2;
    en = 0;
    kinds_inst.sample();
    v = 9;
    en = 1;
    kinds_inst.sample();
    v = 3;
    kinds_inst.sample();
    v = 0;
    kinds_inst.sample();
    // dflt: both bins; excl: b[1] of b[1] and b[2]; gated: both bins; mixed: sized[0], one,
    // arr[2] of 5 bins; xx: low and <b[1],b[1]> of 3 bins
    `checkr(kinds_inst.get_inst_coverage(), 100.0 * (1.0 + 1.0 / 2 + 1.0 + 3.0 / 5 + 2.0 / 3) / 5);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
