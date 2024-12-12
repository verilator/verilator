// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t(/*AUTOARG*/
   // inputs
   clk
);
   input clk;
   bit [31:0] outA;
   bit [31:0] outB;

   subA subA(.out(outA));
   subB subB(.out(outB));

   always @(posedge clk) begin
      if (outA == `VALUE_A && outB == `VALUE_B) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Mismatch\n");
         $stop;
      end
   end
endmodule
