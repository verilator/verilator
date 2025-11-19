// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module m1;
  initial begin
    m2.fin;
  end
endmodule

module m2;
  task fin;
    $write("*-* All Finished *-*\n");
    $finish;
  endtask
endmodule

// Test --top picks this config
config cfg12;
  design work.m1 m2;  // Test both modules listed, library.cell, and cell w/o library
endconfig
