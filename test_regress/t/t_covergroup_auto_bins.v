// DESCRIPTION: Verilator: Verilog Test module
//
// Test automatic bins: bins auto[N]
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  /* verilator lint_off CMPCONST */
  logic [2:0] data;   // 3-bit: 0-7
  logic [3:0] data4;  // 4-bit: exercises width<64 path in maxVal computation
  logic [63:0] data64;  // 64-bit: exercises width>=64 (UINT64_MAX) path

  covergroup cg;
    coverpoint data {
      bins auto[4];  // Should create 4 bins: [0:1], [2:3], [4:5], [6:7]
    }
  endgroup

  // 4-bit auto bins: exercises (width < 64) path: maxVal = (1<<4)-1 = 15
  covergroup cg_4bit;
    coverpoint data4 {
      bins auto[4];  // Creates 4 bins: [0:3], [4:7], [8:11], [12:15]
    }
  endgroup

  // 4-bit auto bins with ignore_bins: exercises excluded-value skip path
  covergroup cg_4bit_excl;
    coverpoint data4 {
      ignore_bins bad = {0};  // value 0 excluded from auto expansion
      bins auto[4];
    }
  endgroup

  // auto_bin_max=2 on 64-bit: exercises numTotalValues=UINT64_MAX path
  covergroup cg2;
    option.auto_bin_max = 2;
    coverpoint data64;
  endgroup
  /* verilator lint_on CMPCONST */

  initial begin
    automatic cg       cg_inst      = new;
    automatic cg_4bit  cg4_inst     = new;
    automatic cg_4bit_excl cg4e_inst = new;
    automatic cg2      cg2_inst     = new;

    // Sample 3-bit cg: one value per bin
    data = 0; cg_inst.sample();
    data = 2; cg_inst.sample();
    data = 5; cg_inst.sample();
    data = 7; cg_inst.sample();

    // Sample 4-bit bins
    data4 = 0;  cg4_inst.sample();   // bin [0:3]
    data4 = 7;  cg4_inst.sample();   // bin [4:7]
    data4 = 10; cg4_inst.sample();   // bin [8:11]
    data4 = 14; cg4_inst.sample();   // bin [12:15]

    // Sample 4-bit with exclusion (value 0 excluded; bins start at 1)
    data4 = 1;  cg4e_inst.sample();
    data4 = 8;  cg4e_inst.sample();

    // Sample both 64-bit range bins
    data64 = 64'd0;                     cg2_inst.sample();  // auto[0]
    data64 = 64'hFFFF_FFFF_FFFF_FFFF;  cg2_inst.sample();  // auto[1]

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
