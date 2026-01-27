// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   wire [32767:0] a = {32768{1'b1}};

   initial begin
      $stop;
   end

endmodule
