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

  covergroup cg_binsof with function sample (bit [6:0] a, bit b, bit enabled);
    cp_a: coverpoint a {
      ignore_bins ignored = {7};
      bins low = {[0 : 1]};
      bins high = {2};
      bins arrayed[] = {3, 4};
      bins rest = default;
    }
    cp_b: coverpoint b {bins low = {0}; bins high = {1}; bins either = {[0 : 1]};}
    // Overlapping coverpoint bins must not count a selected cross bin twice.
    all_products: cross cp_a, cp_b{
      bins combined = binsof (cp_a);
    }
    named: cross cp_a, cp_b{bins selected = binsof (cp_a.low);}
    other_axis: cross cp_a, cp_b{bins selected = (binsof (cp_b.low));}
    array_bins: cross cp_a, cp_b{bins selected = binsof (cp_a.arrayed);}
    overlapping: cross cp_a, cp_b{
      bins lhs = binsof (cp_a.low);
      bins rhs = binsof (cp_b.low);
    }
    guarded: cross cp_a, cp_b iff (enabled) {
      bins selected = binsof (cp_a.low) iff (a == 0);
      bins selected_one = binsof (cp_a.low) iff (a == 1);
    }
    // Non-normal coverpoint bins do not contribute any cross products.
    empty_selection: cross cp_a, cp_b{
      bins ignored = binsof (cp_a.ignored);
      bins defaulted = binsof (cp_a.rest);
    }
  endgroup

  covergroup cg_auto with function sample (bit a, bit b);
    coverpoint a;
    coverpoint b;
    all_products: cross a, b{bins combined = binsof (a);}
  endgroup

  covergroup cg_transition with function sample (bit [6:0] a, bit b);
    cp_a: coverpoint a {bins seq = (0 => 1); bins two = {2};}
    cp_b: coverpoint b;
    transitions: cross cp_a, cp_b{bins selected = binsof (cp_a.seq);}
  endgroup

  covergroup cg_empty with function sample (bit a, bit b);
    cp_a: coverpoint a {ignore_bins ignored = {0, 1};}
    cp_b: coverpoint b;
    empty_product: cross cp_a, cp_b{bins selected = binsof (cp_b);}
  endgroup

  cg_binsof cov = new;
  cg_auto auto_cov = new;
  cg_transition trans_cov = new;
  cg_empty empty_cov = new;

  always @(posedge clk) begin
    if (cyc == 0) begin
      `checkr(cov.get_inst_coverage(), 0.0);
      `checkr(auto_cov.get_inst_coverage(), 0.0);
      `checkr(trans_cov.get_inst_coverage(), 0.0);
      `checkr(empty_cov.get_inst_coverage(), 0.0);
    end
    if (cyc < 18) begin
      cov.sample(7'(cyc / 2), 1'(cyc), cyc != 0);
      auto_cov.sample(1'(cyc / 2), 1'(cyc));
      empty_cov.sample(1'(cyc / 2), 1'(cyc));
      if (cyc < 6) trans_cov.sample(7'(cyc % 3), 1'(cyc / 3));
      if (cyc == 0) begin
        `checkr(cov.get_inst_coverage(), 20.0);
        `checkr(auto_cov.get_inst_coverage(), 60.0);
      end
    end
    else begin
      `checkr(cov.get_inst_coverage(), 100.0);
      `checkr(auto_cov.get_inst_coverage(), 100.0);
      `checkr(trans_cov.get_inst_coverage(), 100.0);
      `checkr(empty_cov.get_inst_coverage(), 100.0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
    ++cyc;
  end
endmodule
