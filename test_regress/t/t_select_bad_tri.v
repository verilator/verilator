// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   reg [72:1] in;
   initial begin
      if (in[(   (1'h0 / 1'b0)   )+:71] != 71'h0) $stop;
   end

endmodule
