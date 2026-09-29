// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Coverpoint bins with 'with' filters (IEEE 1800-2023 19.5.1.1)

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`ifdef verilator
 `define no_optimize(v) $c(v)
`else
 `define no_optimize(v) (v)
`endif
// verilog_format: on

// A constant 'item', which a filter names through its package
package item_pkg;
  localparam bit [2:0] item = 2;
endpackage

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
  typedef enum logic [2:0] {
    C = 4,
    A = 0,
    B = 2,
    D = 6
  } order_t;
  typedef enum logic signed [2:0] {
    MINUS_TWO = -2,
    PLUS_ONE = 1,
    MINUS_ONE = -1,
    PLUS_TWO = 2
  } signed_enum_t;
  localparam logic [70:0] BASE = 71'h1_0000_0000_0000_0000;
  localparam bit [64:0] B65 = 65'h1_0000_0000_0000_0000;
  localparam int item = 7;

  logic [2:0] value;
  logic [1:0] a, b;
  bit enabled;
  int cutoff;
  signed_t signed_value;
  packed_t packed_value;
  enum_t enum_value;
  order_t order_value;
  signed_enum_t signed_enum_value;
  logic [70:0] wide_value;
  logic signed [69:0] wide_signed;
  logic [3:0] nibble;
  logic [17:0] big;
  bit [64:0] w65;
  bit [63:0] q64;

  function automatic bit even(input int candidate);
    return candidate % 2 == 0;
  endfunction

  // Guards true on their second call only
  int with_calls;
  int sized_calls;
  function automatic bit with_second();
    ++with_calls;
    return with_calls == 2;
  endfunction
  function automatic bit sized_second();
    ++sized_calls;
    return sized_calls == 2;
  endfunction

  // Filtered first, then grouped; bins keep the order and duplicates of the values
  covergroup cg_values;
    // One bin of 0, 1, 2
    low: coverpoint value {
      bins low_values = {[0 : 7]} with (item < 3);
    }
    // The range list's 'item' is the parameter; the filter's the candidate
    outer: coverpoint value {
      bins outer_item = {item} with (item == 7);
    }
    // All of the coverpoint's values, a bin for each even one
    evens: coverpoint value {
      bins evens[] = evens with (even(int'(item)));
    }
    // <0, 2>, <4, 6>
    fixed: coverpoint value {
      bins fixed[2] = {[0 : 7]} with (item % 2 == 0);
    }
    // Kept duplicates distribute: <0, 0>, <1, 2>
    dupfix: coverpoint value {
      bins duplicated[2] = {0, 0, 1, 2, 3, 4} with (item < 3);
    }
    // A bin per distinct value, in value order
    dupval: coverpoint value {
      bins duplicate_values[] = {2, 0, 0, 1, 1} with (item < 3);
    }
    dupran: coverpoint value {
      bins duplicate_ranges[] = {[4 : 7], [0 : 3], [2 : 5]} with (item < 6);
    }
    // Filtered values distribute in list order: <5, 1>, <3, 7>
    order: coverpoint value {
      bins ordered[2] = {5, 1, 3, 7} with (1);
    }
    // Runs of values continue over elements
    joined: coverpoint value {
      bins joined = {[0 : 1], [2 : 3], 4} with (item != 3);
    }
    // The bin counts only when enabled
    gated: coverpoint value {
      bins gated = {[0 : 7]} with (item < 3) iff (enabled);
    }
    // A bin without values is not created
    empty: coverpoint value {
      bins some = {0};
      bins none[] = empty with (item > 7);
      bins no_value = {1} with (0);
    }
  endgroup

  // A default bin excludes a filtered bin's values, even when its guard is false
  covergroup cg_default;
    cp: coverpoint value {
      bins gated = {0, 1} with (item < 2) iff (enabled);
      bins remaining = default;
    }
  endgroup

  // Each form of guarded bins counts or reports a value only when its guard is true, while
  // ignore and illegal bins exclude their values from other bins regardless
  covergroup cg_iff;
    counted: coverpoint nibble {
      bins listed = {[0 : 3]} with (item > 0) iff (enabled);
      bins named[] = counted with (item < 2) iff (enabled);
      wildcard bins wild_listed = {4'b00??} with (item > 0) iff (enabled);
      wildcard bins wild_named[] = counted with (item < 2) iff (enabled);
    }
    ignored: coverpoint nibble {
      ignore_bins listed = {[0 : 3]} with (item == 1) iff (enabled);
      ignore_bins named = ignored with (item == 2) iff (enabled);
      wildcard ignore_bins wild_listed = {4'b00??} with (item == 3) iff (enabled);
      wildcard ignore_bins wild_named = ignored with (item == 4) iff (enabled);
      bins probe[] = {[0 : 5]};
    }
    checked: coverpoint value {
      illegal_bins listed = {[0 : 3]} with (item == 1) iff (enabled);
      illegal_bins named = checked with (item == 2) iff (enabled);
      wildcard illegal_bins wild_listed = {3'b0??} with (item == 3) iff (enabled);
      wildcard illegal_bins wild_named = checked with (item == 4) iff (enabled);
      bins probe[] = {[0 : 5]};
    }
  endgroup

  // Bins of values over the 64-bit word boundary, and sized arrays of elements in value order
  covergroup cg_wide;
    single: coverpoint w65 {
      bins b = {[B65 - 8 : B65 + 7]} with (item % 2 == 0);
    }
    values: coverpoint w65 {
      bins b[] = {[B65 - 4 : B65 + 3]} with (item % 2 == 0);
    }
    // <B-8, B-6>, <B-4, B-2>, <B, B+2, B+4, B+6>
    fixed: coverpoint w65 {
      bins b[3] = {[B65 - 8 : B65 + 7]} with (item % 2 == 0);
    }
    // A value per bin: <B-2>, <B-1>, <B>, <B+1>
    unit: coverpoint w65 {
      bins b[4] = {[B65 - 2 : B65 + 1]} with (1);
    }
    // Elements out of order: <B-2, B-1, B+1>, <B-2, B-1, B+1>
    fixed_dup: coverpoint w65 {
      bins b[2] = {[B65 - 2 : B65 + 1], [B65 - 2 : B65 + 1]} with (item != B65);
    }
    // <B-3, B-2>, <B+1, B+2>
    plain: coverpoint w65 {
      bins b[2] = {[B65 - 3 : B65 - 2], [B65 + 1 : B65 + 2]};
    }
    // 256 values per bin
    q_fixed: coverpoint q64 {
      bins b[4] = {[0 : 2047]} with (item % 2 == 0);
    }
  endgroup

  // An illegal bin's guard is evaluated once per sample, as for sized arrays of bins
  covergroup cg_guard;
    filtered: coverpoint value {
      illegal_bins bad = {0} with (1) iff (with_second());
    }
    sized: coverpoint value {
      illegal_bins bad[2] = {0, 1} iff (sized_second());
    }
  endgroup

  // Filtered bins as cross dimensions
  covergroup cg_cross;
    aa: coverpoint a {
      bins even_values[] = aa with (item % 2 == 0);
    }
    bb: coverpoint b {
      bins sized[2] = {[0 : 3], [2 : 3]} with (item != 1);
    }
    xx: cross aa, bb{
      bins two = binsof (aa.even_values) intersect {2};
      bins sized_one = binsof (bb.sized) intersect {3};
    }
  endgroup

  // Coverpoints of various types; the candidate has the coverpoint's type
  covergroup cg_types;
    // -3, -2, -1
    ss: coverpoint signed_value {
      bins negatives[] = {[-3 : 2]} with (item < 0);
    }
    // A filter is true for a nonzero value: all values but in 'none', which has none
    truth: coverpoint signed_value {
      bins all = truth with (1);
      bins real_truth = truth with (0.25);
      bins literal_truth = truth with (bit'("yes"));
      bins wide_truth = truth with (item & 7'sh40);
      bins none = truth with (0);
    }
    // 1, 5, 9, 13, by member and by cast
    pp: coverpoint packed_value {
      bins lo_one[] = {[0 : 15]} with (item.lo == 1);
      bins cast_one[] = {[0 : 15]} with (int'(item) % 4 == 1);
      bins high_two = {[0 : 15]} with (item[3: 2] == 2);
    }
    // Named by value: 2, 4
    ee: coverpoint enum_value {
      bins chosen[] = {ZERO, TWO, FOUR} with (item != ZERO);
      // The coverpoint's name denotes its enumerated values: 0, 2, 4; <0>, <4>
      bins named[] = ee with (1);
      bins named_fixed[2] = ee with (item != TWO);
      bins named_single = ee with (item != TWO);
    }
    // In value order, whatever the declaration order: <0, 2>, <4, 6>
    oe: coverpoint order_value {
      bins named_fixed[2] = oe with (1);
    }
    // In signed value order: -2, -1, 1, 2; <-2>, <-1>, <1, 2>
    se: coverpoint signed_enum_value {
      bins named[] = se with (1);
      bins named_fixed[3] = se with (1);
    }
    // BASE + 1; BASE and BASE + 2; <BASE + 1, BASE + 2>, <BASE + 3>
    ww: coverpoint wide_value {
      bins selected[] = {[BASE : BASE + 71'd3]} with ((item & 71'd3) == 1);
      bins single = {[BASE : BASE + 71'd3]} with (item[0] == 0);
      bins fixed[2] = {[BASE : BASE + 71'd3]} with (item != BASE);
    }
    // -2**69 + 1, -1, 3
    ws: coverpoint wide_signed {
      bins values[] = {-70'sd1, 3, -70'sh20_0000_0000_0000_0000 + 1} with (1);
    }
    // 8, 12, 13
    wild: coverpoint nibble {
      wildcard bins selected[] = {4'b1?0?} with (item != 9);
    }
    // Calls: an SV function of a variable, C++ code, and a system function
    calls: coverpoint big {
      bins sv_function[] = {[0 : 200003]} with (int'(item) < cutoff && int'(item) >= 1);
      bins c_code = {[0 : 9]} with (`no_optimize(int'(item)) % 3 == 0);
      bins pow2[] = {[1 : 20]} with ($countones(item) == 1);
      bins inside_set[] = calls with (item inside {3, [100 : 101]});
    }
  endgroup

  // Automatic bins partition before the filtered exclusions: those of 0, 2, 4
  covergroup cg_ignore;
    cp: coverpoint value {
      ignore_bins odd = {[0 : 7]} with (item % 2 != 0);
      illegal_bins never = {[0 : 7]} with (item == 6);
    }
    // Of auto_bin_max 4, the bins [2:3], [4:5], [6:7] keep values
    auto_max: coverpoint value {
      option.auto_bin_max = 4;
      ignore_bins ignored = {[0 : 1], [5 : 6]} with (1);
    }
    wide: coverpoint wide_value {
      bins values = {[0 : 3]};
      ignore_bins excluded = {3} with (1);
    }
  endgroup

  // Constructor arguments in bounds, counts and filters
  covergroup cg_bounds(input bit [2:0] low, input bit [2:0] high, input bit [2:0] count);
    // <2>, <3, 4>
    upper: coverpoint signed_value {
      bins upper[count] = {[low : $]} with (item <= signed_t'(high));
    }
    // 2, 3, 4
    lower: coverpoint signed_value {
      bins lower[] = {[$ : high]} with (item >= signed_t'(low));
    }
    single: coverpoint signed_value {
      bins single[] = {low} with (1);
    }
  endgroup

  // The coverpoint's name under its guard; a wildcard filter of it has no patterns
  covergroup cg_domain;
    cp: coverpoint value iff (enabled) {
      bins selected[] = cp with (item < 4);
      ignore_bins ignored = cp with (item == 4);
      illegal_bins illegal = cp with (item == 5);
    }
    wild: coverpoint value iff (enabled) {
      wildcard bins selected[] = wild with (item < 4);
      wildcard ignore_bins ignored = wild with (item == 4);
      wildcard illegal_bins illegal = wild with (item == 5);
      wildcard ignore_bins ignored_set = {3'b11?} with (item == 6);
      wildcard illegal_bins illegal_set = {3'b11?} with (item == 7);
    }
    \cp[0] : coverpoint value {
      bins selected = {0, 1} with (item != 0);
      ignore_bins excluded = {2};
      bins remaining = default;
    }
  endgroup

  // Filters are evaluated when constructed: later changes do not redefine the bins
  covergroup cg_capture;
    sc: coverpoint nibble {
      bins b = {[0 : 15]} with (int'(item) < cutoff);
    }
    ar: coverpoint nibble {
      bins b[] = {[0 : 15]} with (int'(item) < cutoff);
    }
  endgroup

  // Members of an enclosing class, for each instance
  class Base;
    bit [2:0] value;
    int minimum;
    int limit;
  endclass

  class Holder extends Base;
    covergroup cg(input int offset);
      cp: coverpoint value {
        bins selected[] = {[minimum + offset : 7]} with (int'(item) < limit);
      }
    endgroup
    function new(int first, int last);
      minimum = first;
      limit = last;
      cg = new(.offset(1));
    endfunction
  endclass

  // 'item' is the candidate only in a filter, which is its scope (IEEE 1800-2023 7.12); elsewhere
  // it is the parameter, 7, as bins and coverpoints named 'item' are no variables (19.5)
  covergroup cg_item_names;
    // The bin 'item' of 0, 1; 7; 6, counted as 'item' is 7; 0, 1, 3
    named: coverpoint value {
      bins item = {[0 : 7]} with (item < 2);
      bins outer = {item};
      bins guarded = {[0 : 7]} with (item == 6) iff (item == 7);
      bins scoped[] = {[0 : 3]} with (item != item_pkg::item);
    }
    // The coverpoint 'item': 6, 7
    item: coverpoint value {
      bins b[] = item with (item > 5);
    }
    flag: coverpoint enabled {
      bins on = {1};
    }
    x: cross named, flag{bins sel = binsof (named.item);}
  endgroup

  // An argument 'item', 3, sets the range list and the array size: 0, 2; <4>, <5>, <6, 7>
  covergroup cg_item_arg(input bit [2:0] item);
    listed: coverpoint value {
      bins b[] = {[0 : item]} with (item % 2 == 0);
    }
    sized: coverpoint value {
      bins b[item] = {[0 : 7]} with (item > 3);
    }
  endgroup

  // Arguments 'item' as the coverpoint expression, whose type the candidate has: 6, 7; 0, 1
  covergroup cg_item_sample with function sample (bit [2:0] item);
    cp: coverpoint item {
      bins b[] = cp with (item > 5);
    }
  endgroup
  covergroup cg_item_ref(ref logic [2:0] item);
    cp: coverpoint item {
      bins b[] = cp with (item < 2);
    }
  endgroup

  // A member 'item' as the coverpoint expression: 2, 3
  class ItemMember;
    bit [2:0] item;
    covergroup cg_member;
      cp: coverpoint item {
        bins b[] = cp with (item inside {[2 : 3]});
      }
    endgroup
    function new;
      cg_member = new;
    endfunction
  endclass

  // Coverpoints and bins whose names join alike, 'p_' of 'q' and 'p' of '_q': 1, 2, 3; 5, 6, 7
  covergroup cg_joined;
    p_: coverpoint value {
      bins q[] = {[0 : 3]} with (item > 0);
    }
    p: coverpoint value {
      bins _q[] = {[4 : 7]} with (item > 4);
    }
  endgroup

  cg_values values_inst = new;
  cg_default default_inst = new;
  cg_cross cross_inst = new;
  cg_types types_inst;
  cg_ignore ignore_inst = new;
  cg_bounds bounds_inst = new(2, 4, 2);
  cg_domain domain_inst = new;
  cg_capture capture_inst;
  cg_guard guard_inst = new;
  cg_wide wide_inst = new;
  cg_iff iff_inst = new;
  cg_item_names item_names_inst = new;
  cg_item_arg item_arg_inst = new(3);
  cg_item_sample item_sample_inst = new;
  cg_item_ref item_ref_inst;
  cg_joined joined_inst = new;
  ItemMember item_member;
  Holder low_holder;
  Holder high_holder;

  initial begin
    wide_value = 0;
    cutoff = 3;
    types_inst = new;
    capture_inst = new;
    cutoff = 10;
    low_holder = new(0, 3);
    high_holder = new(2, 5);
    low_holder.minimum = 7;
    low_holder.limit = 0;
    high_holder.minimum = 7;
    high_holder.limit = 0;

    enabled = 0;
    for (int i = 0; i < 8; ++i) begin
      value = 3'(i);
      values_inst.sample();
      default_inst.sample();
      domain_inst.sample();
    end
    enabled = 1;
    value = 1;
    values_inst.sample();
    default_inst.sample();
    for (int i = 0; i < 5; ++i) begin
      value = 3'(i);
      domain_inst.sample();
    end
    for (int i = 0; i < 6; ++i) begin
      value = 3'(i);
      ignore_inst.sample();
    end

    for (int i = 0; i < 4; ++i) begin
      for (int j = 0; j < 4; ++j) begin
        a = 2'(i);
        b = 2'(j);
        cross_inst.sample();
      end
    end

    for (int i = 0; i < 16; ++i) begin
      signed_value = signed_t'(i % 6 - 3);
      packed_value = packed_t'(i);
      case (i % 3)
        0: enum_value = ZERO;
        1: enum_value = TWO;
        default: enum_value = FOUR;
      endcase
      order_value = i % 2 == 0 ? A : B;
      signed_enum_value = i % 2 == 0 ? MINUS_TWO : MINUS_ONE;
      wide_value = BASE + 71'(i % 4);
      wide_signed = i % 2 == 0 ? -70'sd1 : 70'sd3;
      nibble = 4'(i);
      big = 18'(i);
      types_inst.sample();
    end
    signed_value = 7'sh40;
    types_inst.sample();
    wide_signed = -70'sh20_0000_0000_0000_0000 + 1;
    big = 101;
    types_inst.sample();

    for (int i = 2; i <= 4; ++i) begin
      signed_value = signed_t'(i);
      bounds_inst.sample();
    end
    wide_value = 3;
    ignore_inst.sample();

    nibble = 5;
    capture_inst.sample();
    `checkr(capture_inst.get_inst_coverage(), 0.0);

    low_holder.value = 1;
    high_holder.value = 3;
    low_holder.cg.sample();
    high_holder.cg.sample();
    `checkr(low_holder.cg.get_inst_coverage(), 50.0);
    `checkr(high_holder.cg.get_inst_coverage(), 50.0);
    low_holder.value = 2;
    high_holder.value = 4;
    low_holder.cg.sample();
    high_holder.cg.sample();
    `checkr(low_holder.cg.get_inst_coverage(), 100.0);
    `checkr(high_holder.cg.get_inst_coverage(), 100.0);

    `checkr(values_inst.get_inst_coverage(), 100.0);
    `checkr(default_inst.get_inst_coverage(), 100.0);
    `checkr(cross_inst.get_inst_coverage(), 100.0);
    `checkr(bounds_inst.get_inst_coverage(), 100.0);
    `checkr(item, 7);
    w65 = B65 - 6;
    q64 = 0;
    wide_inst.sample();
    w65 = B65 - 2;
    q64 = 1000;
    wide_inst.sample();
    w65 = B65 + 1;
    q64 = 0;
    wide_inst.sample();
    w65 = B65 + 4;
    q64 = 1000;
    wide_inst.sample();

    // The guards were false when evaluated, so no illegal bin was hit
    value = 0;
    guard_inst.sample();
    `checkd(with_calls, 1);
    `checkd(sized_calls, 1);

    enabled = 0;
    for (int i = 0; i < 6; ++i) begin
      nibble = 4'(i);
      value = 3'(i);
      iff_inst.sample();
    end
    enabled = 1;
    nibble = 1;
    value = 0;
    iff_inst.sample();

    // Each value v is sampled v + 1 times, so the counts tell the values of each bin
    item_ref_inst = new(value);
    item_member = new;
    enabled = 1;
    for (int i = 0; i < 8; ++i) begin
      repeat (i + 1) begin
        value = 3'(i);
        item_member.item = 3'(i);
        item_names_inst.sample();
        item_arg_inst.sample();
        item_sample_inst.sample(3'(i));
        item_ref_inst.sample();
        item_member.cg_member.sample();
        joined_inst.sample();
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
