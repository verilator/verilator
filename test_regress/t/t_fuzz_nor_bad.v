// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module bug_reduction_nor_binary (
    input logic [3:0] var1,
    input logic [3:0] var2,
    output logic [3:0] out1,
    output logic [3:0] out2
);

  assign out1 = var1~|var2;  //< ~| is a unary reduction operator, not a binary infix operator

  assign out2 = var1~&var2;  //< ~& is a unary reduction operator, not a binary infix operator

  // ~^ is legal

endmodule
