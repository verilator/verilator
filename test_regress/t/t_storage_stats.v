// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Julien Margetts.
// SPDX-License-Identifier: CC0-1.0


module ram #(
    parameter aw            = 10,
    parameter dw            =  8,
    parameter depth         = -1
)(
    input  wire              clk,
    input  wire     [aw-1:0] a,
    input  wire              en,
    input  wire              we,
    input  wire     [dw-1:0] d,
    output reg      [dw-1:0] q
);

localparam DEPTH = (depth == -1) ? (2**aw) : depth;

reg  [dw-1:0] mem[DEPTH-1:0];

always @(posedge clk)
    if (en & ~we)
        q <= mem[a];

always @(posedge clk)
    if (we & en)
        mem[a] <= d;

endmodule


module t (/*AUTOARG*/ clk, a, d, q, en, we );

input  wire [15:0] a, d;
input  wire        clk, en, we;
output wire [15:0] q;

wire [15:0] q1;
wire [ 7:0] q2;

reg [15:0] r_1, r_2;

ram #( .aw(12), .dw(16), .depth(4000) ) U_MEM1 ( clk, a[11:0], en ,we, d, q1 );

ram #( .aw(10), .dw(8) ) U_MEM2 ( clk, a[ 9:0], en ,we, d[7:0], q2 );

always @(posedge clk)
begin
    r_1 <= q1 ^ {2{q2}};
    r_2 <= r_1;
end

assign q = r_2;

endmodule
