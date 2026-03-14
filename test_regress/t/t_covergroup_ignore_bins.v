// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test ignore_bins - excluded from coverage

module t (/*AUTOARG*/);
  logic [3:0] data;

  covergroup cg;
    coverpoint data {
      bins low      = {[0:3]};
      bins high     = {[8:11]};
      ignore_bins reserved = {[12:15]};
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    data = 13; cg_inst.sample();  // reserved - ignored
    data = 1;  cg_inst.sample();  // low
    data = 10; cg_inst.sample();  // high

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
