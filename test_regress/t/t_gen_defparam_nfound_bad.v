// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   a a ();
   defparam z.W = 3;  // Bad
endmodule

module a;
   parameter W = 0;
endmodule
