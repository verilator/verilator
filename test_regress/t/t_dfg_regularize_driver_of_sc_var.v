// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub(input in, output out);
  assign out = in;
endmodule

module top(input clk, output out);
  logic one = '1;
  sub sub_inst(.in(one), .out(out));
endmodule
