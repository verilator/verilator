// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`default_nettype none

module t(
    input wire [10:0] i,
    input wire [10:0] j [4],
    input wire [10:0] k [4],

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

    logic [10:0] u [4];
    assign u = j;
    assign u = k;

    logic [10:0] v [4];
    assign v = j;
    assign v[1] = i;

    logic [10:0] w [4];
    assign w[0] = i;
    assign w = j;

    logic [10:0] x [4];
    assign x[3] = i;
    assign x[3][3:2] = ~i[1:0];
    // No warning for w[2]!
    assign x[2][3:2] = ~i[1:0];
    assign x[2][1:0] = ~i[1:0];

    assign o = a ^ u[3] ^ v[3] ^ w[3] ^ x[3];

endmodule
