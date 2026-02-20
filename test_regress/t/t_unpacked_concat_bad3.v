// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Driss Hafdi
// SPDX-License-Identifier: CC0-1.0

module t;

   localparam logic [7:0] TOO_FEW [5] = '{0, 1, 2**8-1};  // Bad

   initial begin
      $display("%p", TOO_FEW);
      $stop;
   end
endmodule
