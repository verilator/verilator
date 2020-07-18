// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   integer a, b;

   reg [2:0][2:0] array;

   initial begin
      foreach (array);  // no index

      foreach (array.array[a]); // not supported

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
