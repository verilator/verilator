// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test large cross coverage with sparse map implementation

module t(/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  int cyc = 0;

  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] c;
  logic [3:0] d;

  covergroup cg @(posedge clk);
    option.per_instance = 1;

    // Each coverpoint has 3 bins, total cross: 3*3*3*3 = 81 bins
    // This exceeds threshold of 64, so should use sparse map
    cp_a: coverpoint a {
      bins a0 = {0,1,2,3,4};
      bins a1 = {5,6,7,8,9};
      bins a2 = {10,11,12,13,14,15};
    }

    cp_b: coverpoint b {
      bins b0 = {0,1,2,3,4};
      bins b1 = {5,6,7,8,9};
      bins b2 = {10,11,12,13,14,15};
    }

    cp_c: coverpoint c {
      bins c0 = {0,1,2,3,4};
      bins c1 = {5,6,7,8,9};
      bins c2 = {10,11,12,13,14,15};
    }

    cp_d: coverpoint d {
      bins d0 = {0,1,2,3,4};
      bins d1 = {5,6,7,8,9};
      bins d2 = {10,11,12,13,14,15};
    }

    // 4-way cross: 3*3*3*3 = 81 bins (> 64 threshold, uses sparse map)
    cross_abcd: cross cp_a, cp_b, cp_c, cp_d;
  endgroup

  cg cg_inst = new;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    // Generate some cross coverage
    a <= cyc[3:0];
    b <= cyc[7:4];
    c <= cyc[3:0];  // Intentionally correlate some
    d <= cyc[7:4];

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
