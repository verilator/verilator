// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Lane Brooks
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   wire  A;

   pullup p1(A);
   pulldown p2(A);

endmodule
