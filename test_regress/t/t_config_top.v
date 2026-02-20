// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module m1;
  initial $stop;
endmodule

module m2;
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

// not defined: module m3;

config cfg1;
  design m1;
endconfig : cfg1  // Test end label

// Check --top picks this config
config cfg2;
  design m2;  // Test without library name
endconfig

config cfg3;
  design work.m3;
endconfig
