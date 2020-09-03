// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2012 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/);

`define ASSERT(x) initial if (!(x)) $stop
   // See IEEE 6.20.2 on value parameters

   localparam unsigned [63:0] UNSIGNED =64'h99934567_89abcdef;
   localparam signed   [63:0] SIGNED  =64'sh99934567_89abcdef;
   localparam real REAL=1.234;
   `ASSERT(UNSIGNED > 0);
   `ASSERT(SIGNED < 0);

   // bullet 1
   localparam A1_WIDE = UNSIGNED;
   `ASSERT($bits(A1_WIDE)==64);

   localparam A2_REAL = REAL;
   `ASSERT(A2_REAL == 1.234);

   localparam A3_SIGNED = SIGNED;
   `ASSERT($bits(A3_SIGNED)==64 && A3_SIGNED < 0);

   localparam A4_EXPR = (2'b01 + 2'b10);
   `ASSERT($bits(A4_EXPR)==2 && A4_EXPR==2'b11);

   // bullet 2
   localparam [63:0] B_UNSIGNED = SIGNED;
   `ASSERT($bits(B_UNSIGNED)==64 && B_UNSIGNED > 0);

   // bullet 3
   localparam signed C_SIGNED = UNSIGNED;
   `ASSERT($bits(C_SIGNED)==64 && C_SIGNED < 0);

   localparam unsigned C_UNSIGNED = SIGNED;
   `ASSERT($bits(C_UNSIGNED)==64 && C_UNSIGNED > 0);

   // bullet 4
   // verilator lint_off WIDTH
   localparam signed [59:0] D_SIGNED = UNSIGNED;
   `ASSERT($bits(D_SIGNED)==60 && D_SIGNED < 0);
   // verilator lint_on WIDTH

   // verilator lint_off WIDTH
   localparam unsigned [59:0] D_UNSIGNED = SIGNED;
   `ASSERT($bits(D_UNSIGNED)==60 && D_UNSIGNED > 0);
   // verilator lint_on WIDTH

   // bullet 6
   localparam UNSIZED = 23;
   `ASSERT($bits(UNSIZED)>=32);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
