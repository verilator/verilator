// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   localparam TEN = 10;
   localparam string PCTPCT = "%%";

   if (0) begin
      $info;
      $info("User elaboration-time info");
      $info("Percent=%% PctPct=%s Ten=%0d", PCTPCT, TEN);
      $warning;
      $warning("User elaboration-time warning");
      $warning(1);  // Check can convert arguments to format
      $error("User elaboration-time error");
   end

   initial begin
      $info;
      $info("User run-time info");
      $info("Percent=%% PctPct=%s Ten=%0d", PCTPCT, TEN);
      $warning;
      $warning("User run-time warning");
      $warning(1);  // Check can convert arguments to format

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
