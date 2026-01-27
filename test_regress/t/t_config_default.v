// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  // Test config allows selecting two different libraries for these instances
  m1 u_1();
  m2 u_2();
  final $write("*-* All Finished *-*\n");
endmodule

config cfg1;
    design t;
    // resolve liba, then libb
    default liblist liba libb ;
endconfig
