// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   integer file;
   integer i;

   initial begin
      $fscanf(file, "%l", i);  // Bad
      $fscanf(file, "%m", i);  // Bad
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
