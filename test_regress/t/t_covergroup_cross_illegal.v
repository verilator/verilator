// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d: got=%f exp=%f\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;

  covergroup cg_iff with function sample (
      bit a, bit b, bit enabled, bit bad_enabled, bit ignore_enabled
  );
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    illegal_last: cross cp_a, cp_b iff (enabled) {
      bins normal = binsof (cp_a);
      ignore_bins ignored = binsof (cp_a) intersect {1} iff (ignore_enabled);
      illegal_bins forbidden = binsof (cp_a) intersect {1} && binsof (cp_b) intersect {
        1
      } iff (bad_enabled);
    }
    illegal_first: cross cp_a, cp_b iff (enabled) {
      illegal_bins forbidden = binsof (cp_a) intersect {1} && binsof (cp_b) intersect {
        1
      } iff (bad_enabled);
      illegal_bins forbidden_again = binsof (cp_a) intersect {1} && binsof (cp_b) intersect {
        1
      } iff (bad_enabled);
      ignore_bins ignored = binsof (cp_a) intersect {1} iff (ignore_enabled);
      bins normal = binsof (cp_a);
    }
  endgroup

  covergroup cg_plain with function sample (bit a, bit b);
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    cx: cross cp_a, cp_b{
      bins normal = binsof (cp_a);
      ignore_bins ignored = binsof (cp_a) intersect {1};
      illegal_bins forbidden = binsof (cp_a) intersect {1} && binsof (cp_b) intersect {1};
    }
    only_illegal: cross cp_a, cp_b{
      illegal_bins forbidden = binsof (cp_a) intersect {1} && binsof (cp_b) intersect {1};
    }
  endgroup

  covergroup cg_multi with function sample (
      bit a, bit b, bit enabled, bit bad_enabled, bit ignore_enabled
  );
    cp_a: coverpoint a iff (enabled) {
      bins zero = {0};
      bins one = {1};
      bins either = {[0 : 1]};
      bins seq = (0 => 1);
    }
    cp_b: coverpoint b {
      bins zero = {0};
      bins one = {1};
      bins either = {[0 : 1]};
    }
    cx: cross cp_a, cp_b{
      bins normal = binsof (cp_a);
      ignore_bins ignored = binsof (cp_a.one);
      illegal_bins forbidden = binsof (cp_a.one) && binsof (cp_b.one);
    }
    guarded: cross cp_a, cp_b iff (enabled) {
      bins normal = binsof (cp_a);
      ignore_bins ignored = binsof (cp_a.one) iff (ignore_enabled);
      illegal_bins forbidden = binsof (cp_a.one) && binsof (cp_b.one) iff (bad_enabled);
      illegal_bins forbidden_seq = binsof (cp_a.seq) iff (bad_enabled);
    }
  endgroup

  cg_iff iff_cov = new;
  cg_plain plain_cov = new;
  cg_multi multi_cov = new;

  always @(posedge clk) begin
    case (cyc)
      0: iff_cov.sample(1, 1, 0, 1, 1);
      1: iff_cov.sample(1, 1, 1, 0, 1);
      2: iff_cov.sample(1, 1, 1, 1, 0);
      3: iff_cov.sample(1, 1, 1, 1, 1);
      4: iff_cov.sample(1, 1, 1, 0, 0);
      5: iff_cov.sample(0, 0, 1, 1, 1);
      6, 7, 8, 9: plain_cov.sample(1'((cyc - 6) / 2), 1'(cyc));
      10, 11, 12, 13: multi_cov.sample(1'((cyc - 10) / 2), 1'(cyc), cyc != 13, cyc == 12, 1);
      14: multi_cov.sample(1, 1, 1, 0, 1);
      15: multi_cov.sample(1, 1, 1, 1, 0);
      16: begin
`ifdef VERILATOR
        `checkd($c32("Verilated::threadContextp()->errorCount()"), 12);
`endif
        `checkr(iff_cov.get_inst_coverage(), 100.0);
        `checkr(plain_cov.get_inst_coverage(), 100.0);
        `checkr(multi_cov.get_inst_coverage(), 100.0);
        $write("*-* All Finished *-*\n");
        $finish;
      end
      default: `stop;
    endcase
    ++cyc;
  end
endmodule
