// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Noam Gallmann.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t(/*AUTOARG*/);
   localparam int SIZES [3:0] = '{1,2,3,4};
   typedef int    calc_sums_t [3:0];

   localparam int SUMS_ARRAY [3:0] = calc_sums_array(SIZES, 4);
   function calc_sums_t calc_sums_array(int s[3:0], int n);
      int sum = 0;
      for (int ii = 0; ii < n; ++ii) begin
         sum = sum + s[ii];
         calc_sums_array[ii] = sum;
      end
   endfunction

`ifndef VERILATOR
   localparam int SUMS_DYN [3:0] = calc_sums_dyn(SIZES, 4);
`endif
   function calc_sums_t calc_sums_dyn(int s[], int n);
      int sum = 0;
      for (int ii = 0; ii < n; ++ii) begin
         sum = sum + s[ii];
         calc_sums_dyn[ii] = sum;
      end
   endfunction

   initial begin
      `checkh(SIZES[0], 4);
      `checkh(SIZES[1], 3);
      `checkh(SIZES[2], 2);
      `checkh(SIZES[3], 1);

      `checkh(SUMS_ARRAY[0], 4);
      `checkh(SUMS_ARRAY[1], 7);
      `checkh(SUMS_ARRAY[2], 9);
      `checkh(SUMS_ARRAY[3], 10);

`ifndef VERILATOR
      `checkh(SUMS_DYN[0], 1);
      `checkh(SUMS_DYN[1], 3);
      `checkh(SUMS_DYN[2], 6);
      `checkh(SUMS_DYN[3], 10);
`endif
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
