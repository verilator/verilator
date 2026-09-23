// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

// Test that '0 and '1 bin values fill to the coverpoint width

module t;
  bit [31:0] insn;
  bit [7:0] b8;
  bit [1:0] mode;

  covergroup cg;
    cp_insn: coverpoint insn {
      bins zeros = {'0};
      bins ones = {'1};
      bins one = {1};
    }
    cp_b8: coverpoint b8 {
      bins hi = {[8'h80 : '1]};
      bins lo = {['0 : 8'h7f]};
    }
    cp_mode: coverpoint mode {bins m = {3};}
    cx: cross cp_mode, cp_insn;
  endgroup

  cg cg_i = new;

  initial begin
    mode = 3;
    insn = 32'hffff_ffff;
    b8 = 8'hff;
    cg_i.sample();
    insn = 32'h0;
    b8 = 8'h01;
    cg_i.sample();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
