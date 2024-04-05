// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t (
    input wire [3:0] a,
    input wire [3:0] b,
    input wire [3:0] c,
    output wire [3:0] x,
    output wire [3:0] y,
    output wire [3:0] z,
    output wire [ 0:0] w1,
    output wire [ 7:0] w8,
    output wire [15:0] w16,
    output wire [31:0] w32,
    output wire [63:0] w64a,
    output wire [63:0] w64b,
    output wire [62:0] w63,
    output wire [95:0] w96
);

    assign x = ~a & ~b;
    assign y = ~b & ~c;
    assign z = ~c & ~a;
    assign w1 = x[0];
    assign w8 = {8{x[1]}};
    assign w16 = {2{w8}};
    assign w32 = {2{w16}};
    assign w64a = {2{w32}};
    assign w64b = {2{~w32}};
    assign w63 = 63'({2{~w32}});
    assign w96 = 96'(w64a);

endmodule
