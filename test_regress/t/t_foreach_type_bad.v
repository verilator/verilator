// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
endclass

module t;

   real r;

   bit  b[2];

   Cls c;

   initial begin
      foreach (c[i]);  // bad type

      foreach (r[i]);  // no loop var

      foreach (b[i, j, k]);  // extra loop var

      foreach (r[, i]);  // no loop var and extra

      $stop;
   end

endmodule
