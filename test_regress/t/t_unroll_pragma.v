// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_DISABLE
 `define PRAGMA /*verilator unroll_disable*/
`elsif TEST_FULL
 `define PRAGMA /*verilator unroll_full*/
`elsif TEST_NONE
 `define PRAGMA
`endif

module t (/*AUTOARG*/);

   int i, j;

   // This must always unroll
   for (genvar g = 0; g < 10; ++g) begin
      initial $c("gened();");
   end

   initial begin
      // Test a loop smaller than --unroll-count
      `PRAGMA
      for (i = 0; i < 2; ++i) begin
         `PRAGMA
         for (j = 0; j < 2; ++j) begin
            $c("small();");
         end
      end
      // Test a loop larger than --unroll-count
      `PRAGMA
      for (i = 0; i < 5; ++i) begin
        `PRAGMA
         for (j = 0; j < 5; ++j) begin
            $c("large();");
         end
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
