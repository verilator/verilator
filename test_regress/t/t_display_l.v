// DESCRIPTION: Verilator: $display() test for %l
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Todd Strader
// SPDX-License-Identifier: CC0-1.0

module t;

   initial begin
      assert (0 == 0) else $fatal(2, "%l %m : %d", 0);
      $display("%l %m");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
