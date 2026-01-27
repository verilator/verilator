// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   Pub pub();

   localparam ZERO = 0;
   if (ZERO) Dead dead();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module Pub;

   // verilator public_module

   // no signals here

endmodule

module Dead;
   // verilator public_module
endmodule
