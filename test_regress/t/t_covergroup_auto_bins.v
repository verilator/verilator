// DESCRIPTION: Verilator: Verilog Test module
//
// Test automatic bins: bins auto[N]
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [2:0] data;  // 3-bit: 0-7
  logic [3:0] data4;  // 4-bit signal
  logic [63:0] data64;  // 64-bit signal
  logic signed [7:0] sdata;  // signed 8-bit: -128..127
  logic [69:0] data70;  // wider than 64 bits

  covergroup cg;
    coverpoint data {
      bins auto[4];  // Should create 4 bins: [0:1], [2:3], [4:5], [6:7]
    }
  endgroup

  // 4-bit signal with auto[4]: creates 4 equal-width bins covering [0:15]
  covergroup cg_4bit;
    coverpoint data4 {
      bins auto[4];  // Creates 4 bins: [0:3], [4:7], [8:11], [12:15]
    }
  endgroup

  // 4-bit auto bins with one value excluded by ignore_bins
  covergroup cg_4bit_excl;
    coverpoint data4 {
      ignore_bins bad = {0};  // value 0 excluded from auto expansion
      bins auto[4];
    }
  endgroup

  // 64-bit signal with auto_bin_max=2: creates 2 bins covering the full 64-bit range
  covergroup cg2;
    option.auto_bin_max = 2;
    coverpoint data64;
  endgroup

  // Signed values partition in value order, 51 values per bin, the last bin also holding the
  // remainder: [-128:-78], [-77:-27], [-26:24], [25:75], [76:127]
  covergroup cg_signed;
    coverpoint sdata {
      bins auto[5];
    }
  endgroup

  // Wider than 64 bits: 5 bins of 2^70/5 values, the last bin also holding the remainder
  covergroup cg_70bit;
    coverpoint data70 {
      bins auto[5];
    }
  endgroup

  // The runtime computes the values of each wide bin for exclusions, carrying between words:
  // ignoring every value of auto[1] leaves it without values, so out of the coverage
  covergroup cg_70bit_excl;
    coverpoint data70 {
      bins auto[5];
      ignore_bins all_of_1 = {[70'd236118324143482260684 : 70'd472236648286964521367]};
    }
  endgroup

  // More bins than values: one bin per value
  covergroup cg_many;
    coverpoint data {
      bins auto[16];
    }
  endgroup

  // Crosses select an implicit automatic bin by its reported name, also when exclusions make
  // the cross select at run time
  covergroup cg_cross_auto;
    cp_a: coverpoint data;
    cp_ax: coverpoint data {
      ignore_bins zero = {0};
    }
    cp_b: coverpoint data4 {
      bins one = {1};
    }
    x: cross cp_a, cp_b{bins sel = binsof (cp_a.auto_2);}
    xx: cross cp_ax, cp_b{bins sel = binsof (cp_ax.auto_2);}
  endgroup

  initial begin
    automatic cg cg_inst = new;
    automatic cg_4bit cg4_inst = new;
    automatic cg_4bit_excl cg4e_inst = new;
    automatic cg2 cg2_inst = new;
    automatic cg_signed cgs_inst = new;
    automatic cg_70bit cg70_inst = new;
    automatic cg_70bit_excl cg70x_inst = new;
    automatic cg_many cgm_inst = new;
    automatic cg_cross_auto cgx_inst = new;

    // Sample 3-bit cg: one value per bin - 4 bins: [0:1],[2:3],[4:5],[6:7]
    data = 0; cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 25.0);
    data = 2; cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 50.0);
    data = 5; cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 75.0);
    data = 7; cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // Sample 4-bit bins - 4 bins: [0:3],[4:7],[8:11],[12:15]
    data4 = 0;
    cg4_inst.sample();  // bin [0:3]
    `checkr(cg4_inst.get_inst_coverage(), 25.0);
    data4 = 7;
    cg4_inst.sample();  // bin [4:7]
    `checkr(cg4_inst.get_inst_coverage(), 50.0);
    data4 = 10;
    cg4_inst.sample();  // bin [8:11]
    `checkr(cg4_inst.get_inst_coverage(), 75.0);
    data4 = 14;
    cg4_inst.sample();  // bin [12:15]
    `checkr(cg4_inst.get_inst_coverage(), 100.0);

    // Sample 4-bit with exclusion (value 0 excluded; 4 auto bins for remaining values)
    data4 = 1;
    cg4e_inst.sample();
    `checkr(cg4e_inst.get_inst_coverage(), 25.0);
    data4 = 8;
    cg4e_inst.sample();
    `checkr(cg4e_inst.get_inst_coverage(), 50.0);

    // Sample 64-bit cg2 - two bins: [0:2^63-1], [2^63:2^64-1]
    data64 = 64'd0;
    cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 50.0);
    data64 = 64'hFFFF_FFFF_FFFF_FFFF;
    cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 100.0);

    // Sample the signed bins at their boundaries
    sdata = -128;
    cgs_inst.sample();
    `checkr(cgs_inst.get_inst_coverage(), 20.0);
    sdata = -78;
    cgs_inst.sample();  // still the first bin
    `checkr(cgs_inst.get_inst_coverage(), 20.0);
    sdata = -77;
    cgs_inst.sample();
    `checkr(cgs_inst.get_inst_coverage(), 40.0);
    sdata = 24;
    cgs_inst.sample();
    `checkr(cgs_inst.get_inst_coverage(), 60.0);
    sdata = 75;
    cgs_inst.sample();
    `checkr(cgs_inst.get_inst_coverage(), 80.0);
    sdata = 127;
    cgs_inst.sample();
    `checkr(cgs_inst.get_inst_coverage(), 100.0);

    // Sample the wide bins at their boundaries
    data70 = 70'd0;
    cg70_inst.sample();
    `checkr(cg70_inst.get_inst_coverage(), 20.0);
    data70 = 70'd236118324143482260683;
    cg70_inst.sample();  // last value of the first bin
    `checkr(cg70_inst.get_inst_coverage(), 20.0);
    data70 = 70'd236118324143482260684;
    cg70_inst.sample();
    `checkr(cg70_inst.get_inst_coverage(), 40.0);
    data70 = 70'd472236648286964521368;
    cg70_inst.sample();
    `checkr(cg70_inst.get_inst_coverage(), 60.0);
    data70 = 70'd944473296573929042735;
    cg70_inst.sample();  // last value of the fourth bin
    `checkr(cg70_inst.get_inst_coverage(), 80.0);
    data70 = '1;
    cg70_inst.sample();  // in the remainder of the last bin
    `checkr(cg70_inst.get_inst_coverage(), 100.0);

    // Sample one of the 4 bins with values
    data70 = 70'd0;
    cg70x_inst.sample();
    `checkr(cg70x_inst.get_inst_coverage(), 25.0);

    // Sample one of the 8 single-value bins
    data = 7;
    cgm_inst.sample();
    `checkr(cgm_inst.get_inst_coverage(), 12.5);

    // Hit each 'sel' cross bin, and one automatic cross bin
    data4 = 1;
    data = 2;
    cgx_inst.sample();
    data = 5;
    cgx_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
