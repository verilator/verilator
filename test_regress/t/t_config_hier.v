// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test several ways of using config to specify different hierarchies When done,
// have a .py file using --work to select each config, and have a .out golden
// match file to make sure get expected results.

module m1;
  initial $stop;
endmodule

module c2_bb;
  initial $display("c2_bb %%m=%m %%l=%l");
endmodule

module c2_b;

  bb u_bb();

  initial $display("c2_b %%m=%m %%l=%l");
endmodule

module t;

  m1 u_1();

  final $write("*-* All Finished *-*\n");

endmodule

config cfg21;
  design t;
  instance t.u_1 use work.cfg2 :config;
endconfig

config cfg22;
  design t;
  instance t.u_1 use cfg2 :config;
endconfig

config cfg31;
  design t;
  cell work.m1 use work.cfg2 :config;
endconfig

config cfg32;
  design t;
  cell m1 use cfg2 :config;
endconfig

config cfg41;
  design t;
  cell work.m1 use work.cfg2;  // :config; implied as no conflict
endconfig

// Base usage
config cfg2;
  design c2_b;
  instance c2_b.u_bb use work.c2_bb;
endconfig
