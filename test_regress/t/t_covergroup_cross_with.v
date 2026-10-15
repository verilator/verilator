// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Cross bins with 'with' filters (IEEE 1800-2023 19.6.1.2): when the covergroup is constructed,
// a filter selects the bin tuples with a value tuple for which it is true, or as many as
// 'matches' requires

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  typedef logic signed [6:0] signed_t;
  typedef struct packed {
    logic [1:0] hi;
    logic [1:0] lo;
  } packed_t;
  typedef enum logic [2:0] {
    ZERO = 0,
    TWO = 2,
    FOUR = 4
  } enum_t;
  localparam logic [70:0] BASE = 71'h1_0000_0000_0000_0000;

  logic [1:0] a, b;
  logic [3:0] nibble;
  signed_t signed_value;
  packed_t packed_value;
  enum_t enum_value;
  logic [70:0] wide_value;
  bit enabled;
  int cutoff;
  int calls;  // Evaluations of keep()

  import "DPI-C" function bit dpi_keep(input int value, input int bound);

  function automatic bit keep(input int value, input int bound);
    ++calls;
    return value < bound;
  endfunction

  // Selections composed with, and of, filters
  covergroup cg_select;
    aa: coverpoint a {
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
    bb: coverpoint b {
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
    xx: cross aa, bb{
      bins equal = xx with (aa == bb);  // <lo,lo>, <hi,hi>
      bins sum_five = xx with (aa + bb == 5);  // <hi,hi>
      bins compound = (binsof (aa.lo) && binsof (bb)) with (aa == bb);  // <lo,lo>
      bins conjunction = binsof (aa.hi) && binsof (bb) with (aa == bb);  // <hi,hi>
      bins nested = (xx with (aa <= bb)) with (aa == bb);  // <lo,lo>, <hi,hi>
      // <lo,lo>, <hi,hi>
      bins combined = binsof (aa.lo) with (aa == bb) || binsof (bb.hi) with (aa + bb == 5);
      bins one_item = xx with (aa > 2);  // <hi,lo>, <hi,hi>
      bins negated = !binsof (aa.lo) with (bb == 0);  // <hi,lo>
      bins intersected = binsof (aa) intersect {1} with (aa == bb);  // <lo,lo>
      bins none = xx with (0);  // No bin tuple, so no bin
      bins all = xx with (1);
    }
  endgroup

  // Each cross item has its coverpoint's type
  covergroup cg_typed;
    ss: coverpoint signed_value {
      bins neg = {[-3 : -1]};
      bins nonneg = {[0 : 2]};
    }
    pp: coverpoint packed_value {
      bins lo_one = {1, 5};
      bins lo_two = {2, 6};
    }
    ee: coverpoint enum_value;
    ww: coverpoint wide_value {
      bins first = {[BASE : BASE + 71'd1]};
      bins second = {[BASE + 71'd2 : BASE + 71'd3]};
    }
    x_sp: cross ss, pp{
      bins neg_lo_one = x_sp with (ss < 0 && pp[1:0] == 1);  // <neg,lo_one>
    }
    x_ew: cross ee, ww{
      bins two_second = x_ew with (ee == TWO && ww > BASE + 71'd1);  // <TWO,second>
    }
  endgroup

  // Values ignore_bins and illegal_bins exclude are in no value tuple; cross exclusions
  // selected by filters remove bin tuples from other bins
  covergroup cg_exclusions;
    aa: coverpoint a {
      bins low = {[0 : 1]};
      bins high = {[2 : 3]};
      ignore_bins skipped = {3};
    }
    bb: coverpoint b {
      bins low = {[0 : 1]};
      bins high = {[2 : 3]};
      illegal_bins bad = {0};
    }
    xx: cross aa, bb{
      bins skipped_value = xx with (aa == 3);  // No bin tuple
      bins bad_value = xx with (bb == 0);  // No bin tuple
      bins equal = xx with (aa == bb);  // <low,low>, as <high,high> is ignored
      ignore_bins high_sum = binsof (aa.high) with (aa + bb >= 5);  // <high,high>
      illegal_bins wrong = binsof (bb.low) with (aa == 2 && bb == 1) iff (enabled);  // <high,low>
    }
  endgroup

  // An excluded value ending a range of a bin is followed by the bin's next range
  covergroup cg_gap;
    aa: coverpoint a {
      bins ends = {0, 3};
      ignore_bins zero = {0};
    }
    bb: coverpoint b {bins all = {[0 : 3]};}
    xx: cross aa, bb{
      bins three = xx with (aa == 3);  // <ends,all>
    }
  endgroup

  // Wildcard bins whose values overlap, and a wildcard exclusion
  covergroup cg_wildcard;
    nn: coverpoint nibble {
      wildcard bins odd = {4'b???1};
      wildcard bins high = {4'b1???};
      wildcard ignore_bins skipped = {4'b11?1};
    }
    bb: coverpoint b {
      bins low = {[0 : 1]};
      bins high = {[2 : 3]};
    }
    xx: cross nn, bb{
      bins odd_high = binsof (nn.odd) with (nn > 8);  // 9 and 11: <odd,low>, <odd,high>
      bins high_odd = binsof (nn.high) with (nn > 12 && nn % 2 == 1);  // Skipped: no bin tuple
      bins high_even = binsof (nn.high) with (nn % 2 == 0) && binsof (bb.low);  // <high,low>
    }
  endgroup

  // Bins whose values the coverpoints compute when constructed
  covergroup cg_constructed;
    aa: coverpoint a {
      bins even[] = aa with (item % 2 == 0);  // even[0], even[2]
    }
    bb: coverpoint b {
      bins sized[2] = {[0 : 3]};  // {0, 1}, {2, 3}
    }
    xx: cross aa, bb{
      bins three = xx with (aa + bb == 3);  // <even[0],sized[1]>, <even[2],sized[0]>
    }
  endgroup

  // A signed wildcard value narrower than its coverpoint has the values of its sign extension
  covergroup cg_extended;
    ss: coverpoint signed_value {wildcard bins even = {4'sb?0?0};}  // -8, -6, 0, 2
    bb: coverpoint b {
      bins low = {[0 : 1]};
      bins high = {[2 : 3]};
    }
    xx: cross ss, bb{
      bins last = xx with (ss == 2 && bb == 3);  // <even,high>, of the last value of 'even'
    }
  endgroup

  // A transition bin's values are the last of its sequences, which state exclusions keep
  covergroup cg_transition;
    tt: coverpoint a {
      bins rise = (0 => 1), (2 => 3);
      ignore_bins one = {1};
    }
    bb: coverpoint b {
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
    xx: cross tt, bb{
      bins ends_one = xx with (tt == 1);  // <rise,lo>, <rise,hi>
    }
  endgroup

  // A coverpoint without bins leaves no bin tuple
  covergroup cg_empty;
    aa: coverpoint a {
      bins none[] = aa with (item > 3);
    }
    bb: coverpoint b;
    xx: cross aa, bb{
      bins entire = xx;
      bins filtered = xx with (1);
    }
  endgroup

  // Coverpoints named for their variables, which the filter's cross items hide
  covergroup cg_alias;
    coverpoint a;
    coverpoint b;
    xx: cross a, b{
      bins equal = xx with (a == b);  // <auto_0,auto_0>, ..., <auto_3,auto_3>
    }
  endgroup

  // Filters calling functions are evaluated when an instance is constructed, with its arguments
  covergroup cg_runtime(input int extra);
    aa: coverpoint a {
      option.weight = 0;
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
    bb: coverpoint b {
      option.weight = 0;
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
    xx: cross aa, bb{
      bins sv_function = xx with (keep(int'(aa) + int'(bb), cutoff + extra));
      bins dpi_function = xx with (dpi_keep(int'(aa) + int'(bb), cutoff + extra));
      bins second_only = xx with (dpi_keep(int'(bb), cutoff));
      bins rest = xx;
    }
  endgroup

  // A 'matches' clause selects the bin tuples with as many value tuples for which the filter is
  // true, or all for '$'.  Of 'aa' and 'nn', <lo,over> and <hi,over> have 24 value tuples, and
  // <lo,rest> and <hi,rest> 8.
  covergroup cg_matches;
    aa: coverpoint a {
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
    nn: coverpoint nibble {
      // 12 values, each once, of an interval or an earlier pattern too: 1, 3, 5, 7, 8 to 15
      wildcard bins over = {4'b???1, 4'b1???, 4'b?1?1};
      bins rest = {0, 2, 4, 6};
    }
    xx: cross aa, nn{
      bins exact = xx with (aa[0] == nn[0]) matches 12;  // <lo,over>, <hi,over>
      bins short = xx with (aa[0] == nn[0]) matches 13;  // No bin tuple, so no bin
      bins distinct = xx with (nn != 0) matches 25;  // No bin tuple
      // Value tuples of all items, though the filter reads one
      bins unread = xx with (aa[0] == 0) matches 12;  // <lo,over>, <hi,over>
      bins all_lo = xx with (aa < 2) matches $;  // <lo,over>, <lo,rest>
      bins all_nonzero = xx with (nn != 0) matches $;  // <lo,over>, <hi,over>
      // 'matches' has higher precedence than '&&' and '||'
      bins conjunction = binsof (aa.lo) with (nn != 0) matches 24 && binsof (nn.over);  // <lo,over>
      bins disjunction = binsof (aa.hi) || xx with (nn != 0) matches 24;  // All but <lo,rest>
      bins nested = (xx with (nn != 0) matches 24) with (aa == 0);  // <lo,over>
      bins over_64_bits = xx with (nn != 0) matches 65'h1_0000_0000_0000_0018;  // No bin tuple
    }
  endgroup

  // Counts of an instance's arguments, when it is constructed
  covergroup cg_count(input int count, input bit [64:0] wide_count);
    aa: coverpoint a {
      option.weight = 0;
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
    nn: coverpoint nibble {
      option.weight = 0;
      bins over = {[8 : 15], 1, 3, 5, 7};
      bins rest = {0, 2, 4, 6};
    }
    xx: cross aa, nn{
      bins counted = xx with (aa[0] == nn[0]) matches count;  // Of 12: <lo,over>, <hi,over>
      bins wide = xx with (aa[0] == nn[0]) matches wide_count;  // As 'counted'
      bins all = xx;
      bins high = binsof (aa.hi);
    }
  endgroup

  // An excluded interval skips values of several intervals and patterns of a bin at once
  covergroup cg_skip;
    aa: coverpoint a {bins lo = {[0 : 1]};}
    nn: coverpoint nibble {
      wildcard bins mixed = {0, 2, 4, 12, 4'b?001, 4'b01?0};  // 9, 12
      ignore_bins skipped = {[0 : 6]};
    }
    xx: cross aa, nn{
      bins all = xx with (nn > 6) matches 4;  // <lo,mixed>
      bins over = xx with (nn > 6) matches 5;  // No bin tuple
    }
  endgroup

  // A filter of an embedded covergroup reads the enclosing object's members, and a count its
  // instance constants (IEEE 1800-2023 19.5)
  class Holder;
    bit [1:0] x;
    bit [1:0] y;
    int bound;
    const int half;
    covergroup cg;
      xp: coverpoint x {
        option.weight = 0;
        bins lo = {[0 : 1]};
        bins hi = {[2 : 3]};
      }
      yp: coverpoint y {
        option.weight = 0;
        bins lo = {[0 : 1]};
        bins hi = {[2 : 3]};
      }
      xy: cross xp, yp{
        bins under = xy with (int'(xp) + int'(yp) < bound);
        bins rest = xy;
        // Of 3 of 4 value tuples for a bound of 5, not <hi,hi>, of 1
        bins counted = xy with (int'(xp) + int'(yp) < bound) matches half;
        bins high = binsof (xp.hi);
      }
    endgroup
    function new(int limit);
      bound = limit;
      half = (limit + 1) / 2;
      cg = new;
    endfunction
  endclass

  cg_select select_inst = new;
  cg_typed typed_inst = new;
  cg_exclusions exclusions_inst = new;
  cg_gap gap_inst = new;
  cg_wildcard wildcard_inst = new;
  cg_extended extended_inst = new;
  cg_constructed constructed_inst = new;
  cg_transition transition_inst = new;
  cg_empty empty_inst = new;
  cg_alias alias_inst = new;
  cg_matches matches_inst = new;
  cg_skip skip_inst = new;
  cg_count count_inst = new(12, 12);
  cg_count over_count_inst = new(13, 65'h1_0000_0000_0000_000c);
  cg_runtime low_inst;
  cg_runtime high_inst;
  Holder low_holder;
  Holder high_holder;

  initial begin
    // Selected when constructed: with a cutoff of 1, of <lo,lo> only; with 4 + 1, of all
    cutoff = 1;
    low_inst = new(0);
    cutoff = 4;
    high_inst = new(1);
    `checkd(calls > 0, 1);
    calls = 0;
    // Later changes do not redefine the bins
    cutoff = 0;
    a = 3;
    b = 3;
    low_inst.sample();
    high_inst.sample();
    `checkr(low_inst.get_inst_coverage(), 25.0);  // rest
    `checkr(high_inst.get_inst_coverage(), 100.0);
    // The bin tuple <lo,lo> was selected, though the values sampled fail the filters
    a = 1;
    b = 1;
    low_inst.sample();
    `checkr(low_inst.get_inst_coverage(), 100.0);
    `checkd(calls, 0);

    low_holder = new(1);
    high_holder = new(5);
    low_holder.x = 3;
    low_holder.y = 3;
    high_holder.x = 3;
    high_holder.y = 3;
    low_holder.cg.sample();
    high_holder.cg.sample();
    `checkr(low_holder.cg.get_inst_coverage(), 50.0);  // rest, high
    `checkr(high_holder.cg.get_inst_coverage(), 75.0);  // Not counted

    enabled = 0;
    for (int i = 0; i < 4; ++i) begin
      for (int j = 0; j < 4; ++j) begin
        a = 2'(i);
        b = 2'(j);
        select_inst.sample();
        constructed_inst.sample();
        empty_inst.sample();
        alias_inst.sample();
        gap_inst.sample();
        if (j != 0) exclusions_inst.sample();  // Not the illegal value
      end
    end
    for (int i = 0; i < 16; ++i) begin
      nibble = 4'(i);
      b = 2'(i);
      wildcard_inst.sample();
    end
    // <lo,rest>, of 'all' only
    a = 0;
    nibble = 0;
    count_inst.sample();
    over_count_inst.sample();
    `checkr(count_inst.get_inst_coverage(), 25.0);
    `checkr(over_count_inst.get_inst_coverage(), 50.0);
    for (int i = 0; i < 4; ++i) begin
      for (int j = 0; j < 16; ++j) begin
        a = 2'(i);
        nibble = 4'(j);
        matches_inst.sample();
        skip_inst.sample();
      end
    end
    for (int i = -8; i < 8; ++i) begin
      for (int j = 0; j < 4; ++j) begin
        signed_value = signed_t'(i);
        b = 2'(j);
        extended_inst.sample();
      end
    end
    // Rising from 0 to 1, with b low then high
    for (int i = 0; i < 4; ++i) begin
      a = 2'(i % 2);
      b = i < 2 ? 2'd0 : 2'd2;
      transition_inst.sample();
    end
    for (int i = 0; i < 16; ++i) begin
      signed_value = signed_t'(i % 6 - 3);
      packed_value = packed_t'(i % 2 != 0 ? 1 : 2);
      enum_value = i % 3 == 0 ? ZERO : i % 3 == 1 ? TWO : FOUR;
      wide_value = BASE + 71'(i % 4);
      typed_inst.sample();
    end
    `checkr(select_inst.get_inst_coverage(), 100.0);
    `checkr(typed_inst.get_inst_coverage(), 100.0);
    `checkr(exclusions_inst.get_inst_coverage(), 100.0);
    `checkr(gap_inst.get_inst_coverage(), 100.0);
    `checkr(wildcard_inst.get_inst_coverage(), 100.0);
    `checkr(extended_inst.get_inst_coverage(), 100.0);
    `checkr(constructed_inst.get_inst_coverage(), 100.0);
    `checkr(transition_inst.get_inst_coverage(), 100.0);
    `checkr(empty_inst.get_inst_coverage(), 100.0);
    `checkr(alias_inst.get_inst_coverage(), 100.0);
    `checkr(matches_inst.get_inst_coverage(), 100.0);
    `checkr(skip_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
