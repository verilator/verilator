// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d: got=%f exp=%f\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t;
  covergroup cg_group with function sample (bit a, bit b);
    option.cross_auto_bin_max = 0;
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    ab: cross cp_a, cp_b{
      bins zero_zero = binsof (cp_a) intersect {0} && binsof (cp_b) intersect {0};
    }
  endgroup

  covergroup cg_cross with function sample (bit a, bit b);
    cp_a: coverpoint a {
      option.cross_auto_bin_max = 0;
    }
    cp_b: coverpoint b;
    ab: cross cp_a, cp_b{option.cross_auto_bin_max = 1;}
  endgroup

  cg_group group_cov = new;
  cg_cross cross_cov = new;

  task automatic check_coverage(real expected);
    `checkr(group_cov.get_inst_coverage(), expected);
    `checkr(cross_cov.get_inst_coverage(), expected);
  endtask

  initial begin
    check_coverage(0.0);
    for (int i = 0; i < 4; ++i) begin
      group_cov.sample(1'(i / 2), 1'(i));
      cross_cov.sample(1'(i / 2), 1'(i));
      // IEEE 1800-2023 19.11: the mean of cp_a, cp_b, and the 4-bin cross
      case (i)
        0: check_coverage((50.0 + 50.0 + 25.0) / 3);
        1: check_coverage((50.0 + 100.0 + 50.0) / 3);
        2: check_coverage((100.0 + 100.0 + 75.0) / 3);
        3: check_coverage(100.0);
        default: `stop;
      endcase
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
