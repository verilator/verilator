// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test for --binary --vpi runtime library loading.  The design provides its
// own clock (so the simulation has Verilog event activity); the VPI library
// (t_flag_main_vpi.cpp), loaded at runtime via +verilator+vpi+, observes
// 'count' via a cbValueChange callback and calls $finish after MAX_TICKS
// edges.  Signals are public so the library can reach them by name
// (requires --public-flat-rw).
module t;

   reg clk /*verilator public_flat_rw*/;
   reg [31:0] count /*verilator public_flat_rw*/;

   initial begin
      clk = 0;
      count = 0;
   end

   // Self-driving clock: the design itself keeps the simulation alive
   always #5 clk = ~clk;

   always @(posedge clk) count <= count + 1;

endmodule
