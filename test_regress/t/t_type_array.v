// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   int arr [5];
   localparam type arr_type = type(arr);
   arr_type arr_prime;

   initial begin
      arr[3] = 123;
      arr_prime = arr;
      if (arr_prime[3] != 123) $stop();
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
