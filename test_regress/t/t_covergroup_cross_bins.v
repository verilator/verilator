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

  covergroup cg_order with function sample (bit [1:0] a, bit b, bit enabled);
    cp_a: coverpoint a {
      bins values[] = {[0 : 3]};
    }
    cp_b: coverpoint b;
    normal_first: cross cp_a, cp_b{
      bins combined = binsof (cp_a);
      bins empty = binsof (cp_a) intersect {0};
      ignore_bins ignored = binsof (cp_a) intersect {0} iff (enabled);
      illegal_bins forbidden = binsof (cp_a) intersect {3} iff (enabled);
      ignore_bins empty_ignore = binsof (cp_a) intersect {7};
      illegal_bins empty_illegal = binsof (cp_a) intersect {7};
    }
    exclusions_first: cross cp_a, cp_b{
      illegal_bins forbidden = binsof (cp_a) intersect {3} iff (enabled);
      ignore_bins ignored = binsof (cp_a) intersect {0} iff (enabled);
      bins empty = binsof (cp_a) intersect {0};
      bins combined = binsof (cp_a);
    }
  endgroup

  covergroup cg_auto with function sample (bit [1:0] a, bit b, bit enabled);
    cp_a: coverpoint a {
      bins values[] = {[0 : 3]};
    }
    cp_b: coverpoint b;
    cx: cross cp_a, cp_b{
      ignore_bins ignored = binsof (cp_a) intersect {0} iff (enabled);
      illegal_bins forbidden = binsof (cp_a) intersect {3} iff (enabled);
    }
  endgroup

  covergroup cg_static_cross with function sample (bit a, bit b, bit enabled);
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    xx: cross cp_a, cp_b{
      bins entire = xx;
      bins zero = xx && binsof (cp_a) intersect {0};
      bins one = binsof (cp_a) intersect {1} && xx;
      bins union_left = xx || binsof (cp_a) intersect {0};
      bins union_right = binsof (cp_b) intersect {1} || xx;
      bins grouped = (xx && binsof (cp_a) intersect {0}) || (binsof (cp_b) intersect {1} && (xx));
      bins guarded = xx iff (enabled);
    }
    \cross.ref : cross cp_a, cp_b{bins entire = \cross.ref ;}
  endgroup

  covergroup cg_overlap with function sample (bit [1:0] a, bit b);
    cp_a: coverpoint a {
      bins low = {[0 : 1]};
      bins high = {[2 : 3]};
      bins either = {[0 : 3]};
    }
    cp_b: coverpoint b {
      bins zero = {0};
      bins one = {1};
      bins either = {[0 : 1]};
    }
    cx: cross cp_a, cp_b{
      bins combined = binsof (cp_a);
      bins entire = cx;
      bins empty = binsof (cp_a.low) && binsof (cp_b.zero);
      ignore_bins ignored = binsof (cp_a.low);
      illegal_bins forbidden = binsof (cp_a.high) && binsof (cp_b.one) iff (0);
    }
  endgroup

  covergroup cg_wide with function sample (bit [6:0] a, bit b);
    cp_a: coverpoint a {
      bins values[] = {[0 : 64]};
    }
    cp_b: coverpoint b;
    whole: cross cp_a, cp_b{
      bins entire = whole;
      bins tail = whole && binsof (cp_a) intersect {64};
    }
    cx: cross cp_a, cp_b{
      bins combined = binsof (cp_a);
      bins partial = binsof (cp_a) intersect {[30 : 34]};
      bins sparse = binsof (cp_a) intersect {0, 64};
      bins empty = binsof (cp_a) intersect {[31 : 33]};
      ignore_bins ignored = binsof (cp_a) intersect {[31 : 33]};
      illegal_bins forbidden = binsof (cp_a) intersect {64} iff (0);
    }
  endgroup

  covergroup cg_empty with function sample (bit [1:0] a, bit b);
    cp_a: coverpoint a {
      bins values[] = {[0 : 3]};
    }
    cp_b: coverpoint b;
    cx: cross cp_a, cp_b{
      bins empty = cx;
      ignore_bins ignored = cx;
      illegal_bins forbidden = cx iff (0);
    }
  endgroup

  covergroup cg_transition with function sample (bit a, bit b);
    cp_a: coverpoint a {
      bins seq = (0 => 1);
      bins zero = {0};
      bins one = {1};
    }
    cp_b: coverpoint b;
    cx: cross cp_a, cp_b{
      bins combined = binsof (cp_a);
      ignore_bins ignored = binsof (cp_a.seq);
      illegal_bins forbidden = binsof (cp_a.one) && binsof (cp_b) intersect {1} iff (0);
    }
  endgroup

  covergroup cg_zero_product with function sample (bit a, bit b);
    cp_a: coverpoint a {
      ignore_bins ignored = {0, 1};
    }
    cp_b: coverpoint b;
    cx: cross cp_a, cp_b{
      bins empty = cx;
      ignore_bins ignored = binsof (cp_b);
      illegal_bins forbidden = binsof (cp_b);
    }
  endgroup

  covergroup cg_three with function sample (bit a, bit b, bit c);
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    cp_c: coverpoint c;
    cx: cross cp_a, cp_b, cp_c{
      bins combined = binsof (cp_a);
      ignore_bins ignored = binsof(cp_a) intersect {0}
          && (binsof(cp_b) intersect {1} || !binsof(cp_c) intersect {
        1
      });
      illegal_bins forbidden = binsof(cp_a) intersect {1}
          && binsof(cp_b) intersect {1} && binsof(cp_c) intersect {
        1
      } iff (0);
    }
  endgroup

  cg_order order_cov = new;
  cg_auto auto_cov = new;
  cg_static_cross static_cov = new;
  cg_overlap overlap_cov = new;
  cg_wide wide_cov = new;
  cg_empty empty_cov = new;
  cg_transition trans_cov = new;
  cg_three three_cov = new;
  cg_zero_product zero_cov = new;

  always @(posedge clk) begin
    if (cyc < 8) begin
      order_cov.sample(2'(cyc / 2), 1'(cyc), cyc < 6 && 1'(cyc));
      auto_cov.sample(2'(cyc / 2), 1'(cyc), cyc < 6 && 1'(cyc));
      static_cov.sample(1'(cyc / 2), 1'(cyc), cyc < 4);
      overlap_cov.sample(2'(cyc / 2), 1'(cyc));
      empty_cov.sample(2'(cyc / 2), 1'(cyc));
      trans_cov.sample(1'(cyc), 1'(cyc / 2));
      three_cov.sample(1'(cyc / 4), 1'(cyc / 2), 1'(cyc));
      zero_cov.sample(1'(cyc / 2), 1'(cyc));
      if (cyc == 1) begin
        `checkr(order_cov.get_inst_coverage(), 37.5);
        `checkr(auto_cov.get_inst_coverage(), 30.0);
      end
      if (cyc == 5) begin
        `checkr(order_cov.get_inst_coverage(), 87.5);
        `checkr(auto_cov.get_inst_coverage(), 90.0);
      end
    end
    if (cyc < 65) begin
      wide_cov.sample(7'(cyc), 0);
      wide_cov.sample(7'(cyc), 1);
    end
    else begin
      `checkr(order_cov.get_inst_coverage(), 100.0);
      `checkr(auto_cov.get_inst_coverage(), 100.0);
      `checkr(static_cov.get_inst_coverage(), 100.0);
      `checkr(overlap_cov.get_inst_coverage(), 100.0);
      `checkr(wide_cov.get_inst_coverage(), 100.0);
      `checkr(empty_cov.get_inst_coverage(), 100.0);
      `checkr(trans_cov.get_inst_coverage(), 100.0);
      `checkr(three_cov.get_inst_coverage(), 100.0);
      `checkr(zero_cov.get_inst_coverage(), 100.0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
    ++cyc;
  end
endmodule
