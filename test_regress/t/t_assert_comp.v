// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   if (0) begin
      $info("User compile-time info");
      $warning("User compile-time warning");
      $error("User compile-time error");
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
