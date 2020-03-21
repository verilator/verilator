// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   parameter [ BMSB : BLSB ] B = A[23:20]; // 3
   parameter A = 32'h12345678;
   parameter BLSB = A[16+:4];  // 4
   parameter BMSB = A[7:4]; // 7

   initial begin
      if (B !== 4'h3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
