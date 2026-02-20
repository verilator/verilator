// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2011 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   sub sub ();
endmodule

module sub #(parameter WIDTH=X, parameter X=WIDTH)
   ();
endmodule
