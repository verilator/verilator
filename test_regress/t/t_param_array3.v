// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   parameter int SIZES [3:0] = '{1,2,3,4};
   typedef int calc_sums_t [3:0];

   function calc_sums_t calc_sums;
      int sum = 0;
      for (int i=0; i<4; i++) begin
         sum = sum + SIZES[i];
         calc_sums[i] = sum;
         //TODO: calc_sums[i][31:0] = sum;
      end
   endfunction

   parameter int SUMS[3:0] = calc_sums();

   initial begin
      if (SUMS[0] != 4) $stop;
      if (SUMS[1] != 4+3) $stop;
      if (SUMS[2] != 4+3+2) $stop;
      if (SUMS[3] != 4+3+2+1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
