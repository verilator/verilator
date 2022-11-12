// DESCRIPTION: Verilator: Test of select from constant
//
// This tests issue 508, bit select of constant fails
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      randcase  // Bad all zero weights
        0 : $stop;
      endcase
      $finish;
   end

endmodule
