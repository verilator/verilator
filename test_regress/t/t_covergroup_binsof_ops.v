// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d: got=%f exp=%f\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;

  covergroup cg_sets with function sample (bit [6:0] a, bit b, bit enabled);
    cp_a: coverpoint a {
      bins low = {[0 : 3]};
      bins overlap = {[2 : 5]};
      bins high = {[6 : 7]};
      bins arrayed[] = {8, 9};
      ignore_bins ignored = {12};
      bins rest = default;
    }
    cp_b: coverpoint b {bins zero = {0}; bins one = {1}; bins both = {0, 1};}
    ranges: cross cp_a, cp_b{
      // Intersect selects entire bins, including values outside the filter.
      bins middle = binsof (cp_a) intersect {
        [3 : 4]
      };
      bins named = binsof (cp_a.arrayed) intersect {9};
      bins lower = binsof (cp_a) intersect {[$ : 0]};
      bins upper = binsof (cp_a) intersect {[9 : $]};
      bins values = binsof (cp_a) intersect {1, [7 : 8]};
      bins absent = binsof (cp_a) intersect {30};
      bins outside_domain = binsof (cp_a) intersect {128};
      bins reversed = binsof (cp_a) intersect {[5 : 3]};
    }
    logic_ops: cross cp_a, cp_b{
      bins negated = !binsof (cp_a.low);
      bins negated_range = !binsof (cp_a) intersect {[3 : 4]};
      bins named_not_hit = !binsof (cp_a.low) intersect {3};
      bins named_not_miss = !binsof (cp_a.low) intersect {4};
      bins either = binsof (cp_a.low) || binsof (cp_b.one);
      bins both = binsof (cp_a.low) && binsof (cp_b.one);
      bins repeated = binsof (cp_a.low) || binsof (cp_a.low);
      bins all_bins = binsof (cp_a.low) || !binsof (cp_a.low);
      bins no_bins = !binsof (cp_a);
      // Distinct bins may overlap in values but never in bin identity.
      bins no_tuple = binsof (cp_a.low) && binsof (cp_a.overlap);
      bins not_hit_negation = binsof (cp_a.low) && !binsof (cp_a.overlap);
      bins excluded = binsof (cp_a.ignored) || binsof (cp_a.rest);
    }
    guarded: cross cp_a, cp_b iff (enabled) {
      bins selected = (binsof(cp_a.low) || binsof(cp_a.arrayed))
                      && binsof(cp_b.one) iff (a != 0);
    }
  endgroup

  covergroup cg_precedence with function sample (bit a, bit b, bit c);
    coverpoint a;
    coverpoint b;
    coverpoint c;
    three_axes: cross a, b, c{
      bins ungrouped = binsof(a) intersect {0}
                      || binsof(b) intersect {0} && binsof(c) intersect {
        1
      };
      bins grouped = (binsof (a) intersect {0} || binsof (b) intersect {
        0
      }) && binsof (c) intersect {
        1
      };
      bins mixed = !binsof (a) intersect {0} && (binsof (b) intersect {0} || !binsof (c) intersect {
        0
      });
    }
  endgroup

  typedef bit signed [6:0] signed_t;
  typedef bit [64:0] wide_t;
  localparam wide_t LOW  = 65'h0_ffff_ffff_ffff_ffff;
  localparam wide_t HIGH = 65'h1_0000_0000_0000_0000;

  covergroup cg_numeric with function sample (signed_t a, wide_t b);
    cp_a: coverpoint a {
      bins negative = {[-4 : -1]};
      bins encoded = {7'b1111111};
      bins encoded_range = {[7'd120 : 7'd127]};
      bins narrow_signed = {-7'sd1};
      bins zero = {0};
      bins positive = {[1 : 4]};
    }
    cp_b: coverpoint b {bins low = {LOW}; bins high = {HIGH};}
    numeric: cross cp_a, cp_b{
      bins negative_high = binsof (cp_a) intersect {[-3 : -2]} && binsof (cp_b) intersect {
        [HIGH : $]
      };
      bins nonnegative_low = !binsof (cp_a) intersect {[$ : -1]} && binsof (cp_b) intersect {LOW};
      bins typed_negative = binsof(cp_a.encoded) intersect {-1}
                            || binsof(cp_a.encoded_range) intersect {
        -2
      };
    }
  endgroup

  covergroup cg_transition with function sample (bit [6:0] a, bit b);
    cp_a: coverpoint a {
      bins first = (0 => 1);
      bins second = (2 => 3);
      bins combined = (0 => 1), (2 => 3);
      bins value = {4};
    }
    cp_b: coverpoint b;
    transitions: cross cp_a, cp_b{
      bins ending_one = binsof (cp_a) intersect {1};
      bins not_ending_one = !binsof (cp_a) intersect {1};
      bins named = binsof (cp_a.combined) intersect {3};
      bins not_initial = binsof (cp_a.first) intersect {0};
    }
  endgroup

  covergroup cg_wildcard with function sample (signed_t a, bit b);
    cp_a: coverpoint a {wildcard bins odd = {7'b??????1}; bins high = {[32 : 35]};}
    cp_b: coverpoint b;
    wildcard_range: cross cp_a, cp_b{
      // Neither endpoint matches, but the interior value 3 does.
      bins interior = binsof (cp_a) intersect {
        [2 : 4]
      };
      bins even = binsof (cp_a) intersect {2};
      bins other = !binsof (cp_a) intersect {[2 : 4]};
      bins signed_pattern = binsof (cp_a.odd) intersect {[-4 : -1]};
    }
  endgroup

  covergroup cg_words with function sample (bit [6:0] a, bit [6:0] b);
    cp_a: coverpoint a {bins values[] = {[0 : 8]};}
    cp_b: coverpoint b {bins values[] = {[0 : 8]};}
    partial: cross cp_a, cp_b{
      bins boundary = binsof (cp_a) intersect {7};
      bins either = binsof (cp_a) intersect {7} || binsof (cp_b) intersect {8};
      bins last_row = binsof (cp_a) intersect {8} && binsof (cp_b) intersect {0};
    }
    all_tuples: cross cp_a, cp_b{bins all_bins = binsof (cp_a);}
  endgroup

  // Check four-state bin identities without relying on four-state sampling.
  covergroup cg_four_state with function sample (logic [2:0] a, bit b);
    cp_a: coverpoint a {bins known = {3'b001}; bins xstate = {3'bx01}; bins zstate = {3'bz01};}
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{
      bins exact_x = binsof (cp_a) intersect {3'bx01};
      bins exact_z = binsof (cp_a) intersect {3'bz01};
      bins not_x = !binsof (cp_a) intersect {3'bx01};
    }
  endgroup

  covergroup cg_narrow_wildcard with function sample (signed_t a, bit b);
    cp_s: coverpoint a {wildcard bins w = {3'sb?01}; ignore_bins outside = {7'sd7};}
    cp_u: coverpoint 7'd1 {wildcard bins w = {3'sb?01};}
    cp_b: coverpoint b;
    signed_values: cross cp_s, cp_b{
      bins positive = binsof (cp_s.w) intersect {1};
      bins negative = binsof (cp_s.w) intersect {-3};
      bins not_expanded = binsof (cp_s.w) intersect {5};
      bins pattern_miss = binsof (cp_s.w) intersect {0};
      bins complement = !binsof (cp_s.w) intersect {5};
    }
    unsigned_values: cross cp_u, cp_b{
      bins positive = binsof (cp_u.w) intersect {1};
      bins not_expanded = binsof (cp_u.w) intersect {5};
    }
  endgroup

  covergroup cg_excluded with function sample (bit [6:0] a, bit b);
    cp_a: coverpoint a {
      bins normal = {[0 : 3]}; ignore_bins ignored = {1}; illegal_bins illegal = {3};
    }
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{
      bins kept = binsof (cp_a.normal) intersect {0};
      bins partial = binsof (cp_a.normal) intersect {[1 : 3]};
      bins removed_ignore = binsof (cp_a.normal) intersect {1};
      bins removed_illegal = binsof (cp_a.normal) intersect {3};
      bins removed_union = binsof (cp_a.normal) intersect {1, 3};
      bins complement = !binsof (cp_a.normal) intersect {1};
    }
  endgroup

  covergroup cg_excluded_wildcard with function sample (bit [6:0] a, bit b);
    cp_a: coverpoint a {
      bins normal = {[0 : 15]};
      wildcard ignore_bins odds = {7'b??????1};
      illegal_bins band = {[4 : 7]};
      ignore_bins empty_range = {[9 : 8]};
    }
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{
      bins kept = binsof (cp_a.normal) intersect {2};
      bins removed_pattern = binsof (cp_a.normal) intersect {1, 9, 15};
      bins removed_range = binsof (cp_a.normal) intersect {[4 : 7]};
      bins removed_union = binsof (cp_a.normal) intersect {[3 : 6]};
    }
  endgroup

  covergroup cg_excluded_wide with function sample (wide_t a, bit b);
    cp_a: coverpoint a {bins normal = {LOW, HIGH}; ignore_bins ignored = {LOW};}
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{
      bins kept = binsof (cp_a.normal) intersect {HIGH};
      bins removed = binsof (cp_a.normal) intersect {LOW};
    }
  endgroup

  covergroup cg_excluded_many with function sample (bit [30:0] a, bit b);
    cp_a: coverpoint a {
      bins whole = {[0 : 31'h7fffffff]};
      // Only the all-ones value remains; enumerating live prefix subsets is exponential.
      wildcard ignore_bins zero_bit = {
        (31'bx & ~31'h00000001), (31'bx & ~31'h00000002), (31'bx & ~31'h00000004),
        (31'bx & ~31'h00000008), (31'bx & ~31'h00000010), (31'bx & ~31'h00000020),
        (31'bx & ~31'h00000040), (31'bx & ~31'h00000080), (31'bx & ~31'h00000100),
        (31'bx & ~31'h00000200), (31'bx & ~31'h00000400), (31'bx & ~31'h00000800),
        (31'bx & ~31'h00001000), (31'bx & ~31'h00002000), (31'bx & ~31'h00004000),
        (31'bx & ~31'h00008000), (31'bx & ~31'h00010000), (31'bx & ~31'h00020000),
        (31'bx & ~31'h00040000), (31'bx & ~31'h00080000), (31'bx & ~31'h00100000),
        (31'bx & ~31'h00200000), (31'bx & ~31'h00400000), (31'bx & ~31'h00800000),
        (31'bx & ~31'h01000000), (31'bx & ~31'h02000000), (31'bx & ~31'h04000000),
        (31'bx & ~31'h08000000), (31'bx & ~31'h10000000), (31'bx & ~31'h20000000),
        (31'bx & ~31'h40000000)
      };
    }
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{bins kept = binsof (cp_a.whole) intersect {[0 : 31'h7fffffff]};}
  endgroup

  covergroup cg_transition_ignore with function sample (bit a, bit b);
    cp_a: coverpoint a {bins seq = (0 => 1); ignore_bins value_only = {1};}
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{bins kept = binsof (cp_a.seq) intersect {1};}
  endgroup

  // State-bin exclusions also apply to exact four-state selections at construction.
  covergroup cg_excluded_four_state with function sample (logic [2:0] a, bit b);
    cp_a: coverpoint a {
      bins states = {3'b001, 3'bx01, 3'bz01};
      ignore_bins xstate = {3'bx01};
      wildcard ignore_bins other = {3'b1?1};
    }
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{
      bins kept = binsof (cp_a.states) intersect {3'bz01};
      bins numeric = binsof (cp_a.states) intersect {1};
      bins removed = binsof (cp_a.states) intersect {3'bx01};
    }
  endgroup

  covergroup cg_registry with function sample (bit a, bit b);
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    selected: cross cp_a, cp_b{
      bins off_diagonal = binsof(cp_a) intersect {0} && binsof(cp_b) intersect {1}
                          || binsof(cp_a) intersect {1} && binsof(cp_b) intersect {
        0
      };
    }
  endgroup

  task automatic sample_retired(bit a, bit b);
    cg_registry transient = new;
    transient.sample(a, b);
  endtask

  cg_sets sets_cov = new;
  cg_precedence precedence_cov = new;
  cg_numeric numeric_cov = new;
  cg_transition transition_cov = new;
  cg_wildcard wildcard_cov = new;
  cg_words words_cov = new;
  cg_four_state four_state_cov = new;
  cg_narrow_wildcard narrow_wildcard_cov = new;
  cg_excluded excluded_cov = new;
  cg_excluded_wildcard excluded_wildcard_cov = new;
  cg_excluded_wide excluded_wide_cov = new;
  cg_excluded_many excluded_many_cov = new;
  cg_transition_ignore transition_ignore_cov = new;
  cg_excluded_four_state excluded_four_state_cov = new;

  always @(posedge clk) begin
    if (cyc == 0) sample_retired(0, 1);
    if (cyc == 1) sample_retired(1, 0);
    if (cyc == 2) sample_retired(0, 0);
    if (cyc < 81) begin
      if (cyc < 24) sets_cov.sample(7'(cyc / 2), 1'(cyc), cyc / 2 != 2);
      if (cyc < 8) precedence_cov.sample(1'(cyc / 4), 1'(cyc / 2), 1'(cyc));
      if (cyc == 8) precedence_cov.sample(1, 0, 0);
      if (cyc < 6)
        numeric_cov.sample(signed_t'(cyc < 2 ? -1 : 2 * (cyc / 2) - 2),
                           (cyc % 2 != 0) ? HIGH : LOW);
      if (cyc < 10) transition_cov.sample(7'(cyc % 5), 1'(cyc / 5));
      if (cyc < 4) wildcard_cov.sample(cyc < 2 ? 7'sd1 : 7'sd32, 1'(cyc));
      if (cyc < 4) begin
        narrow_wildcard_cov.sample(cyc < 2 ? 7'sd1 : -7'sd3, 1'(cyc));
        excluded_cov.sample(cyc < 2 ? 7'd0 : 7'd2, 1'(cyc));
        excluded_wildcard_cov.sample(cyc < 2 ? 7'd0 : 7'd8, 1'(cyc));
        transition_ignore_cov.sample(1'(cyc), 1'(cyc / 2));
      end
      if (cyc < 2) begin
        excluded_wide_cov.sample(HIGH, 1'(cyc));
        excluded_many_cov.sample(31'h7fffffff, 1'(cyc));
      end
      words_cov.sample(7'(cyc / 9), 7'(cyc % 9));
    end
    else begin
      `checkr(sets_cov.get_inst_coverage(), 100.0);
      `checkr(precedence_cov.get_inst_coverage(), 100.0);
      `checkr(numeric_cov.get_inst_coverage(), 100.0);
      `checkr(transition_cov.get_inst_coverage(), 100.0);
      `checkr(wildcard_cov.get_inst_coverage(), 100.0);
      `checkr(words_cov.get_inst_coverage(), 100.0);
      `checkr(four_state_cov.get_inst_coverage(), 0.0);
      `checkr(narrow_wildcard_cov.get_inst_coverage(), 100.0);
      `checkr(excluded_cov.get_inst_coverage(), 100.0);
      `checkr(excluded_wildcard_cov.get_inst_coverage(), 100.0);
      `checkr(excluded_wide_cov.get_inst_coverage(), 100.0);
      `checkr(excluded_many_cov.get_inst_coverage(), 100.0);
      `checkr(transition_ignore_cov.get_inst_coverage(), 100.0);
      `checkr(excluded_four_state_cov.get_inst_coverage(), 0.0);
`ifdef VERILATOR
      `checkd(
          $c32(
          "Verilated::threadContextp()->covergroupRegistryp()->liveInstanceCount(\"cg_registry\")"),
          0);
      `checkd($c32(
              "Verilated::threadContextp()->covergroupRegistryp()->retiredInstanceCount(\"cg_registry\")"
              ), 3);
`endif
      $write("*-* All Finished *-*\n");
      $finish;
    end
    ++cyc;
  end
endmodule
