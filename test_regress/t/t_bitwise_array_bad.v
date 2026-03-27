// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t(
   input [1:0] i,
   output [1:0] o,
   output [1:0] o2
);
   wire [1:0] arr [1:0];
   assign o = arr | 1;
   assign o2 = arr | i + 1;
endmodule
