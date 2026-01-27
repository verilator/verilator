// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   integer a, b;

   reg [2:0][2:0] array;

   initial begin
      foreach (array);  // no index

      foreach (array.array[a]); // not supported

      foreach (array[a.b]);  // no index

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
