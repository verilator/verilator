// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  // Test config allows selecting two different libraries for these instances
  m1 u_1();
  m2 u_2();
  final $write("*-* All Finished *-*\n");
endmodule

config cfg1;
  design t;
  // Use libb's version of m3 for m1 and liba's version of m3 for m2
  instance t.u_1.u_13 liblist libb;
  instance t.u_2.u_23 use liba.m3;
endconfig
