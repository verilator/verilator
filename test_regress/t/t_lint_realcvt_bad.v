// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module sub;

   time t_ok1 = 9ns;  // > 1ns units
   time t_bad1 = 9.001ns;  // < 1ns units
   time t_bad2 = 9.999ns;  // < 1ns units

   time t_ok2 = 9.001us;  // > 1ns units

   time t_bad3 = 9ps;  // < 1ns units

   realtime rt_ok10 = 9.001ns;  // < 1ns units
   realtime rt_ok11 = 9ps;  // < 1ns units

   integer i_ok20 = 23.0; // No warning
   integer i_bad21 = 23.1;

endmodule
