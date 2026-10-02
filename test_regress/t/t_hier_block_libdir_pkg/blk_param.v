// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module blk_param
  import my_pkg::*;
#(
    parameter type T = byte_t,
    parameter byte_t STEP = 1
) (
    input clk,
    output T cnt_o
);
  always @(posedge clk) cnt_o <= cnt_o + T'(STEP);
endmodule
