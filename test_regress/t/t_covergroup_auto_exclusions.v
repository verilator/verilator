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

  // Bin values resolve to the coverpoint's type (IEEE 1800-2023 19.5.7) and bins without
  // values do not count (19.11.1), whether or not the coverpoint has exclusions.  The two
  // covergroups differ only by an ignore_bins that is never hit.
  // verilog_format: off
`define RESOLUTION_BINS \
      bins outside = {[8 : 9]}; \
      bins unknown = {3'bx01}; \
      bins wide = {15}; \
      bins reversed = {[3 : 1]}; \
      bins kept = {[2 : 3]}; \
      bins clipped = {[6 : 10]}; \
      bins values[] = {4, 3'bx11}; \
      bins rest = default;
`define RESOLUTION_CROSS \
    other: coverpoint side; \
    cx: cross cp, other { \
      bins unknown_values = binsof (cp) intersect {3'bx01}; \
      bins kept_values = binsof (cp.kept); \
    }
  // verilog_format: on
  covergroup cg_resolution with function sample (logic [2:0] value, bit side);
    cp: coverpoint value {`RESOLUTION_BINS}
    `RESOLUTION_CROSS
  endgroup

  covergroup cg_resolution_excl with function sample (logic [2:0] value, bit side);
    cp: coverpoint value {
      `RESOLUTION_BINS
      ignore_bins unused = {5};
    }
    `RESOLUTION_CROSS
  endgroup

  // Real bin values keep the integral values they contain (IEEE 1800-2023 19.5.7).
  covergroup cg_real_values with function sample (bit [2:0] value);
    cp: coverpoint value {
      bins two = {2.0};
      bins fraction = {2.5};
      bins far = {100.0};
      bins middle = {[3.5 : 5.5]};
      bins high = {[6.5 : 100.0]};
      bins low = {[-5.0 : 0.5]};
      ignore_bins ignored = {1.0};
    }
    plain: coverpoint value {
      bins two = {2.0};
      bins middle = {[3.5 : 5.5]};
    }
  endgroup

  covergroup cg_real_point with function sample (real value);
    cp: coverpoint value {
      bins low = {[0 : 1]};
      bins middle = {[1.5 : 2.5]};
      bins three = {3.0};
    }
  endgroup

  // More values than one constructor call describes
  covergroup cg_many_values with function sample (bit [9:0] value);
    cp: coverpoint value {
      bins odd = {
        1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29,
        31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59,
        61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89,
        91, 93, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 119,
        121, 123, 125, 127, 129, 131, 133, 135, 137, 139, 141, 143, 145, 147, 149,
        151, 153, 155, 157, 159, 161, 163, 165, 167, 169, 171, 173, 175, 177, 179,
        181, 183, 185, 187, 189, 191, 193, 195, 197, 199, 201, 203, 205, 207, 209,
        211, 213, 215, 217, 219, 221, 223, 225, 227, 229, 231, 233, 235, 237, 239,
        241, 243, 245, 247, 249, 251, 253, 255, 257, 259, 261, 263, 265, 267, 269,
        271, 273, 275, 277, 279, 281, 283, 285, 287, 289, 291, 293, 295, 297, 299,
        301, 303, 305, 307, 309, 311, 313, 315, 317, 319, 321, 323, 325, 327, 329,
        331, 333, 335, 337, 339, 341, 343, 345, 347, 349, 351, 353, 355, 357, 359,
        361, 363, 365, 367, 369, 371, 373, 375, 377, 379, 381, 383, 385, 387, 389,
        391, 393, 395, 397, 399, 401, 403, 405, 407, 409, 411, 413, 415, 417, 419,
        421, 423, 425, 427, 429, 431, 433, 435, 437, 439, 441, 443, 445, 447, 449,
        451, 453, 455, 457, 459, 461, 463, 465, 467, 469, 471, 473, 475, 477, 479,
        481, 483, 485, 487, 489, 491, 493, 495, 497, 499, 501, 503, 505, 507, 509,
        511, 513, 515, 517, 519, 521, 523, 525, 527, 529, 531, 533, 535, 537, 539,
        541, 543, 545, 547, 549, 551, 553, 555, 557, 559, 561, 563, 565, 567, 569,
        571, 573, 575, 577, 579, 581, 583, 585, 587, 589, 591, 593, 595, 597, 599
      };
      ignore_bins ignored = {0};
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
  cg_resolution resolution_cov = new;
  cg_resolution_excl resolution_excl_cov = new;
  cg_real_values real_values_cov = new;
  cg_real_point real_point_cov = new;
  cg_many_values many_values_cov = new;

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
      for (int value = 0; value < 8; ++value) begin
        if (value != 5) begin
          resolution_cov.sample(3'(value), 0);
          resolution_cov.sample(3'(value), 1);
          resolution_excl_cov.sample(3'(value), 0);
          resolution_excl_cov.sample(3'(value), 1);
        end
        real_values_cov.sample(3'(value));
      end
      `checkr(resolution_cov.get_inst_coverage(), 100.0);
      `checkr(resolution_excl_cov.get_inst_coverage(), 100.0);
      `checkr(real_values_cov.get_inst_coverage(), 100.0);
      real_point_cov.sample(1.25);
      `checkr(real_point_cov.get_inst_coverage(), 0.0);
      real_point_cov.sample(0.5);
      real_point_cov.sample(2.0);
      real_point_cov.sample(3.0);
      `checkr(real_point_cov.get_inst_coverage(), 100.0);
      many_values_cov.sample(2);
      `checkr(many_values_cov.get_inst_coverage(), 0.0);
      many_values_cov.sample(599);
      many_values_cov.sample(1);
      `checkr(many_values_cov.get_inst_coverage(), 100.0);
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
