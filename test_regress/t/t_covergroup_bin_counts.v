// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test viewing individual bin hit counts

module t (/*AUTOARG*/);
  logic [3:0] data;

  covergroup cg;
    coverpoint data {
      bins zero = {0};
      bins low  = {[1:3]};
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    data = 0; cg_inst.sample();  // zero: 1
    data = 1; cg_inst.sample();  // low: 1
    data = 2; cg_inst.sample();  // low: 2
    data = 2; cg_inst.sample();  // low: 3

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
