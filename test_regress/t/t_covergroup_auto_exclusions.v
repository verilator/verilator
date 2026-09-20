// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d: got=%f exp=%f\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;

  // IEEE 1800-2023 19.11.1: retain auto_1={2,3}, auto_2={4}, auto_3={7}.
  covergroup cg_partition with function sample (bit [2:0] value);
    option.auto_bin_max = 4;
    cp: coverpoint value {
      ignore_bins ignored = {0, 1, 5, 6};
    }
  endgroup

  covergroup cg_explicit with function sample (bit [2:0] value);
    cp: coverpoint value {
      bins all = {[0 : 7]};
      bins empty = {0, 1};
      bins mixed = {1, 3, 5};
      bins values[] = {0, 2, 4};
      wildcard bins outside_domain = {4'b1???};
      ignore_bins ignored[] = {0, 1};
      illegal_bins forbidden = {5} iff (0);
    }
  endgroup

  covergroup cg_cross with function sample (bit [3:0] a, bit [1:0] b, bit enabled);
    option.auto_bin_max = 4;
    aa: coverpoint a {
      ignore_bins low = {[0 : 3]};
      illegal_bins high = {[12 : 15]} iff (0);
    }
    bb: coverpoint b {
      bins values[] = {[0 : 3]};
      ignore_bins ignored = {1};
    }
    automatic_cross: cross aa, bb;
    xx: cross aa, bb{
      bins empty = binsof (aa) intersect {0} iff (0);
      bins removed = binsof (aa) intersect {8} && binsof (bb) intersect {3} iff (0);
      bins all = xx iff (enabled);
      bins row = binsof (aa) intersect {4} iff (!enabled);
      bins column = binsof (bb.values) intersect {2} iff (enabled);
      bins grouped = (xx && binsof (aa) intersect {8}) || binsof (bb) intersect {2};
      ignore_bins ignored = binsof (aa) intersect {8} && binsof (bb) intersect {3} iff (enabled);
      illegal_bins forbidden = binsof (aa) intersect {4} && binsof (bb) intersect {2} iff (0);
    }
  endgroup

  covergroup cg_wide_cross with function sample (bit [6:0] a, bit b, bit enabled);
    aa: coverpoint a {
      bins low[] = {[0 : 32]};
      bins middle = {[0 : 64]};
      bins high[] = {[33 : 64]};
      bins all = {[0 : 64]};
      ignore_bins ignored = {0};
    }
    bb: coverpoint b;
    xx: cross aa, bb{
      bins empty = binsof (aa.low) intersect {0} iff (0);
      bins disabled = xx iff (0);
      bins enabled_bin = xx iff (enabled);
      bins tail = binsof (aa.all) iff (enabled);
    }
  endgroup

  covergroup cg_empty with function sample (bit [1:0] a, bit [1:0] b);
    aa: coverpoint a {
      ignore_bins ignored = {[0 : 3]} iff (0);
    }
    bb: coverpoint b;
    xx: cross aa, bb{bins empty = xx iff (0);}
  endgroup

  covergroup cg_signed with function sample (bit signed [6:0] value);
    option.auto_bin_max = 3;
    cp: coverpoint value {
      ignore_bins ignored = {[-64 : -23]};
    }
  endgroup

  covergroup cg_wide with function sample (bit [64:0] value);
    option.auto_bin_max = 4;
    cp: coverpoint value {
      ignore_bins ignored = {[65'h0 : 65'h0_7fffffffffffffff]};
    }
  endgroup

  covergroup cg_wild with function sample (bit [64:0] value);
    cp: coverpoint value {
      wildcard bins even_values = {65'bx0};
      wildcard bins odd_values = {65'bx1};
      wildcard ignore_bins ignored = {65'bx0};
    }
  endgroup

  covergroup cg_wild_empty with function sample (bit [64:0] value);
    option.auto_bin_max = 4;
    cp: coverpoint value {
      wildcard ignore_bins even_values = {65'bx0};
      wildcard ignore_bins odd_values = {65'bx1};
    }
  endgroup

  covergroup cg_projection with function sample (bit signed [2:0] value);
    negative: coverpoint value {
      bins keep = {3'sb111};
      wildcard bins empty = {5'b01???};
      wildcard bins signed_empty = {5'sb01???};
      wildcard ignore_bins positive = {4'sb0???};
    }
    positive: coverpoint value {
      bins keep = {3'sb001};
      wildcard ignore_bins negative = {4'sb1???};
    }
  endgroup

  covergroup cg_source_width with function sample (bit signed [6:0] value);
    cp: coverpoint value {
      wildcard bins keep = {2'sbx0};
      ignore_bins ignored = {1};
    }
  endgroup

  covergroup cg_unsigned_pattern with function sample (bit signed [2:0] value);
    cp: coverpoint value {
      wildcard bins all_values = {4'b0???};
      wildcard bins negative_pair = {4'b011?};
      bins negative = {4'b0111};
      ignore_bins ignored = {0};
    }
  endgroup

  covergroup cg_zero_limit with function sample (bit value);
    option.auto_bin_max = 0;
    cp: coverpoint value;
  endgroup

  covergroup cg_signed_wide with function sample (bit signed [64:0] value, bit side);
    option.auto_bin_max = 4;
    cp: coverpoint value {
      ignore_bins ignored = {[$ : 65'sh1_7fffffffffffffff]};
    }
    other: coverpoint side;
    cx: cross cp, other{
      bins negative = binsof (cp) intersect {65'sh1_ffffffffffffffff};
      bins positive = binsof (cp) intersect {65'sh0_8000000000000000} && binsof (other) intersect {
        1
      };
    }
  endgroup

  covergroup cg_pattern_carry with function sample (
      bit [3:0] unsigned_value, bit signed [3:0] signed_value, bit side
  );
    cp_unsigned: coverpoint unsigned_value {
      wildcard bins patterned = {4'b?0?0};
      ignore_bins ignored = {15};
    }
    cp_signed: coverpoint signed_value {
      wildcard bins patterned = {4'sb?0?0};
      ignore_bins ignored = {4'shf};
    }
    other: coverpoint side;
    unsigned_cross: cross cp_unsigned, other{
      bins carry = binsof (cp_unsigned.patterned) intersect {[3 : 9]};
      bins empty = binsof (cp_unsigned.patterned) intersect {[11 : 15]};
    }
    signed_cross: cross cp_signed, other{
      bins carry = binsof (cp_signed.patterned) intersect {[-5 : 1]};
    }
  endgroup

  cg_partition partition_cov = new;
  cg_explicit explicit_cov = new;
  cg_cross cross_cov = new;
  cg_wide_cross wide_cross_cov = new;
  cg_empty empty_cov = new;
  cg_signed signed_cov = new;
  cg_wide wide_cov = new;
  cg_wild wild_cov = new;
  cg_wild_empty wild_empty_cov = new;
  cg_projection projection_cov = new;
  cg_source_width source_width_cov = new;
  cg_unsigned_pattern unsigned_pattern_cov = new;
  cg_zero_limit zero_limit_cov = new;
  cg_signed_wide signed_wide_cov = new;
  cg_pattern_carry pattern_carry_cov = new;

  always @(posedge clk) begin
    if (cyc == 0) begin
      partition_cov.sample(2);
      partition_cov.sample(4);
      partition_cov.sample(7);
      `checkr(partition_cov.get_inst_coverage(), 100.0);
      partition_cov.sample(3);
      explicit_cov.sample(2);
      explicit_cov.sample(3);
      explicit_cov.sample(4);
      `checkr(explicit_cov.get_inst_coverage(), 100.0);
      empty_cov.sample(0, 1);
      empty_cov.sample(3, 2);
      `checkr(empty_cov.get_inst_coverage(), 50.0);
      signed_cov.sample(-22);
      signed_cov.sample(63);
      `checkr(signed_cov.get_inst_coverage(), 100.0);
      signed_cov.sample(-64);
      wide_cov.sample(65'h0_8000000000000000);
      wide_cov.sample(65'h1_0000000000000000);
      wide_cov.sample(65'h1_ffffffffffffffff);
      `checkr(wide_cov.get_inst_coverage(), 100.0);
      wide_cov.sample(0);
      wild_cov.sample(1);
      wild_cov.sample(65'h1_ffffffffffffffff);
      wild_cov.sample(0);
      `checkr(wild_cov.get_inst_coverage(), 100.0);
      wild_empty_cov.sample(0);
      wild_empty_cov.sample(1);
      wild_empty_cov.sample(65'h1_fffffffffffffffe);
      wild_empty_cov.sample(65'h1_ffffffffffffffff);
      projection_cov.sample(-1);
      `checkr(projection_cov.get_inst_coverage(), 50.0);
      projection_cov.sample(1);
      `checkr(projection_cov.get_inst_coverage(), 100.0);
      source_width_cov.sample(-4);
      source_width_cov.sample(2);
      `checkr(source_width_cov.get_inst_coverage(), 0.0);
      source_width_cov.sample(-2);
      source_width_cov.sample(0);
      `checkr(source_width_cov.get_inst_coverage(), 100.0);
      unsigned_pattern_cov.sample(-1);
      `checkr(unsigned_pattern_cov.get_inst_coverage(), 100.0);
      zero_limit_cov.sample(0);
      zero_limit_cov.sample(1);
      signed_wide_cov.sample(-1, 0);
      signed_wide_cov.sample(-1, 1);
      signed_wide_cov.sample(0, 0);
      signed_wide_cov.sample(65'sh0_ffffffffffffffff, 1);
      signed_wide_cov.sample(65'sh1_0000000000000000, 0);
    end
    if (cyc < 8) begin
      if (cyc == 0 || cyc == 1 || cyc == 5 || cyc == 6) partition_cov.sample(3'(cyc));
      if (cyc == 0 || cyc == 1 || cyc >= 5) explicit_cov.sample(3'(cyc));
      cross_cov.sample(cyc < 4 ? 4'd4 : 4'd8, 2'(cyc), 1'(cyc));
    end
    if (cyc == 8) cross_cov.sample(8, 2, 1);
    if (cyc < 16) pattern_carry_cov.sample(4'(cyc), 4'(cyc), 1'(cyc / 2));
    if (cyc < 65) begin
      wide_cross_cov.sample(7'(cyc), 0, 1);
      wide_cross_cov.sample(7'(cyc), 1, 1);
    end
    else begin
      wide_cross_cov.sample(1, 0, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
    ++cyc;
  end
endmodule
