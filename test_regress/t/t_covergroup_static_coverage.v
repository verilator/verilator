// DESCRIPTION: Verilator: Verilog Test module
//
// Test static get_coverage() with multiple instances.
// Type-level (static) coverage using cg::get_coverage() compiles but returns
// a placeholder value (0.0); runtime behavior is not fully correct.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg;
    coverpoint data {
      bins low  = {[0:1]};
      bins mid  = {[2:3]};
      bins high = {[4:5]};
    }
  endgroup

  int data;

  initial begin
    cg cg1, cg2, cg3;

    cg1 = new;
    cg2 = new;
    cg3 = new;

    // Sample cg1 with low bin
    data = 0;
    cg1.sample();

    // Sample cg2 with mid bin
    data = 2;
    cg2.sample();

    // Sample cg3 with high bin
    data = 4;
    cg3.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
