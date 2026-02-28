// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
module t;
   logic [31:0] tmp;
   logic [31:0] tmp2;
   logic [31:0] tmp3;
   initial begin
      tmp = 0;
      $monitor("[%0t] monitor0 %h", $time, tmp);
      while (tmp < 32) begin
         tmp = tmp + 1;
         if ((tmp % 5) == 1) begin
            tmp = tmp + 2;
            tmp = tmp + 1;
         end
         #1;
      end
      $write("*-* All Finished *-*\n");
      $finish();
   end
endmodule
