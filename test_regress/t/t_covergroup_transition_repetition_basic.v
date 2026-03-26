// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a);
    cp: coverpoint a {
      bins cons5  = (3 [*5]);
      bins cons23 = (4 [*2:3]);
      bins goto5  = (5 [->5]);
      bins goto23 = (6 [->2:3]);
      bins nonc5  = (7 [=5]);
      bins nonc23 = (8 [=2:3]);
    }
  endgroup

  cg cov = new;

  task automatic check(int exp_covered);
    int covered_bins;
    int total_bins;
    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != (100.0 * exp_covered) / 6.0) $stop;
    if (covered_bins != exp_covered) $stop;
    if (total_bins != 6) $stop;
  endtask

  initial begin
    repeat (4) cov.sample(3);
    check(0);
    cov.sample(3);
    check(1);

    cov.sample(4);
    check(1);
    cov.sample(4);
    check(2);

    repeat (4) begin
      cov.sample(5);
      cov.sample(0);
    end
    check(2);
    cov.sample(5);
    check(3);

    cov.sample(0);
    cov.sample(6);
    cov.sample(0);
    check(3);
    cov.sample(6);
    check(4);

    repeat (4) begin
      cov.sample(7);
      cov.sample(0);
    end
    check(4);
    cov.sample(7);
    check(5);

    cov.sample(8);
    cov.sample(0);
    check(5);
    cov.sample(8);
    check(6);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
