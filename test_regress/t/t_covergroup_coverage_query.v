// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test querying coverage values via get_inst_coverage

module t (/*AUTOARG*/);
  logic [3:0] data;

  covergroup cg;
    coverpoint data {
      bins low  = {[0:3]};
      bins mid  = {[4:7]};
      bins high = {[8:15]};
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    // Sample low bin - should be 33.3% (1 of 3 bins)
    data = 1;
    cg_inst.sample();
    $display("After low:  %0.1f%%", cg_inst.get_inst_coverage());

    // Sample mid bin - should be 66.7% (2 of 3 bins)
    data = 5;
    cg_inst.sample();
    $display("After mid:  %0.1f%%", cg_inst.get_inst_coverage());

    // Sample high bin - should be 100.0% (3 of 3 bins)
    data = 10;
    cg_inst.sample();
    $display("After high: %0.1f%%", cg_inst.get_inst_coverage());

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
