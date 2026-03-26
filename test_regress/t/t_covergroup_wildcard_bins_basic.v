// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(bit [3:0] a);
    cp: coverpoint a {
      wildcard bins hi      = {4'b1??1};
      wildcard bins mid     = {4'b01??};
      wildcard bins even_lo = {4'b00??} with (!item[0]);
    }
  endgroup

  cg cov = new;

  initial begin
    int covered_bins;
    int total_bins;

    cov.sample(4'b1001);
    if (cov.cp.get_inst_coverage() != (100.0 / 3.0)) $stop;

    cov.sample(4'b0110);
    if (cov.cp.get_inst_coverage() != (200.0 / 3.0)) $stop;

    cov.sample(4'b0010);
    if (cov.cp.get_inst_coverage() != 100.0) $stop;

    covered_bins = 0;
    total_bins = 0;
    if (cov.get_inst_coverage(covered_bins, total_bins) != 100.0) $stop;
    if (covered_bins != 3) $stop;
    if (total_bins != 3) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
