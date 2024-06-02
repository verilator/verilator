// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`default_nettype none

module t(
    input  wire [10:0] i,
    output wire [10:0] o
);
    logic [10:0] a;
    assign a[3:0] = i[3:0];
    assign a[4:1] = ~i[4:1];
    assign a[3] = ~i[3];
    assign a[8:5] = i[8:5];
    assign a[7:6] = ~i[7:6];
    assign a[9] = i[9];
    assign a[9] = ~i[9];
    assign a[10] = i[10];
    assign o = a;
endmodule
