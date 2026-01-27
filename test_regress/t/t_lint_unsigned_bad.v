// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   bit [2:0] uns;

   initial begin
      uns = 1;
      if (uns < 0) $stop;
   end
endmodule
