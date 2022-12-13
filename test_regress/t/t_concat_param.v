// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t
#(
    parameter int cond = 0,

    parameter int len1 = 12,
    parameter logic [len1-1:0] arr1v0 = '0
)
(
);
    localparam logic [len1-1:0] arr1      = 10;
    localparam logic            value1    = '0;

    localparam int total_len = 1 + len1;

    localparam logic [total_len-1:0] offsets_i = {value1, arr1[len1-1:0]};

endmodule: t
