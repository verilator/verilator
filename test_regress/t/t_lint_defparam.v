// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   sub sub ();
   defparam sub.P = 2;

endmodule

module sub;
   parameter P = 6;
   if (P != 0) ;  // Prevent unused
endmodule
