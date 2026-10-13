// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module blk
  import my_pkg::*;
(
    input clk,
    output byte_t cnt_o
);
  always @(posedge clk) cnt_o <= cnt_o + 1;
endmodule
