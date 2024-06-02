// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   interconnect a;

   assign a = 1; // Bad IEEE 6.6.8 - shall not be used in continuous assignment

   initial begin
      a = 2; // Bad IEEE 6.6.8 - shall not be used in procedural assignment
   end

endmodule
