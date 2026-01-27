// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   integer a[];

   initial begin
      if ($bits(a) != 0) $stop;
      a = new [10];
      if ($bits(a) != 10*32) $stop;
   end

endmodule
