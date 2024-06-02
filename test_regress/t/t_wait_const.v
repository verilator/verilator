// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   initial begin
      // This test is separate from t_wait.v because we needed a process with
      // just one wait of a non-zero to see a bug where GCC gave "return value
      // not used"
      // verilator lint_off WAITCONST
      wait (1);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
