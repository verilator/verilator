// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2018 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module top
  (input d,
   output ext0,
   output ext1,
   output extx,
   output extz);

   assign ext0 = (d === 1'b0);
   assign ext1 = (d === 1'b1);
   assign extx = (d === 1'bx);
   assign extz = (d === 1'bz);
endmodule
