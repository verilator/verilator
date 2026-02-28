// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`include "t_pp_lib_inc.vh"
module t();
   wire [`WIDTH-1:0] a;
   library_cell n1(a);
endmodule
