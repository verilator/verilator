// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   localparam type t = logic;  // Fine
   localparam type bad2 = 2;  // Bad
endmodule
