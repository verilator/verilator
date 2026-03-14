// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test dynamic covergroup creation with 'new' operator

module t;

  covergroup cg;
    coverpoint data {
      bins low  = {[0:1]};
      bins high = {[2:3]};
    }
  endgroup

  int data;

  initial begin
    cg cg_inst;

    // Create first dynamic instance
    cg_inst = new;
    data = 0; cg_inst.sample();  // low bin
    data = 2; cg_inst.sample();  // high bin

    // Create second independent instance
    begin
      cg cg2;
      cg2 = new;
      data = 0; cg2.sample();  // low bin
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
