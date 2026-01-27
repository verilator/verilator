// DESCRIPTION: Verilator: Test of select from constant
//
// This tests issue #508, bit select of constant fails
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   initial begin
      randcase  // Bad all zero weights
        0 : $stop;
      endcase
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
