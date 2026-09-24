// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

// Test array bins whose values form consecutive runs, and those that do not

module t;
  bit [11:0] csr;
  bit signed [3:0] s4;
  bit [69:0] wide;
  logic [2:0] x3;
  bit [1:0] mode;

  covergroup cg;
    cp_runs: coverpoint csr {
      bins lo[] = {[12'h100 : 12'h103]};
      bins mixed[] = {12'h200, [12'h204 : 12'h206], 12'h300};
      ignore_bins ig[] = {[12'h400 : 12'h402]};
      illegal_bins il[] = {[12'hF00 : 12'hF01]};
    }
    cp_iff: coverpoint csr iff (mode == 1) {bins g[] = {[12'h100 : 12'h101]};}
    cp_signed: coverpoint s4 {bins s[] = {[0 : 2]};}
    cp_wide: coverpoint wide {bins w[] = {[70'd5 : 70'd6]};}
    cp_xz: coverpoint x3 {bins v[] = {3'b0x1, 3'd2, 3'd3};}
    cp_mode: coverpoint mode {bins m = {1};}
    cx: cross cp_mode, cp_runs;
  endgroup

  cg cg_i = new;

  initial begin
    mode = 1;
    s4 = 1;
    wide = 70'd6;
    x3 = 3'd3;
    csr = 12'h102;
    cg_i.sample();
    csr = 12'h205;
    cg_i.sample();
    csr = 12'h300;
    cg_i.sample();
    csr = 12'h401;
    cg_i.sample();
    csr = 12'h101;
    mode = 0;
    cg_i.sample();
    csr = 12'h005;
    cg_i.sample();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
