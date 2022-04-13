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
    output wire     [dw-1:0] q
);

localparam DEPTH = (depth == -1) ? (2**aw) : depth;

reg  [dw-1:0] mem[DEPTH-1:0];
reg  [dw-1:0] mem2[DEPTH-1:0];
reg  [dw-1:0] mem3[DEPTH-1:0];
reg  [dw-1:0] ramq;

// Simple single port RAM

always @(posedge clk)
    if (en & ~we)
        ramq <= mem[a];

always @(posedge clk)
    if (we & en)
        mem[a] <= d;

// Not a simple RAM, too many writers (on the same source line)

always @(posedge clk)
    if (we & en)
    begin
        mem2[a] <= d; mem2[a+2%DEPTH] <= d+2;
    end

// Not a simple RAM, too many writers

always @(posedge clk)
    if (we & en)
        mem3[a] <= d;
    else if (we ^ en)
        mem3[a+1%DEPTH] <= d+1;

assign q = ramq | mem2[a] | mem3[a];

endmodule


module t (/*AUTOARG*/ clk, a, d, q, en, we );

input  wire [15:0] a, d;
input  wire        clk, en, we;
output wire [15:0] q;

reg [15:0] not_a_RAM[3:0];

initial not_a_RAM = '{4{16'd0}};

wire unused;

reg [31:0] r_unused;

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

assign q = r_2 | not_a_RAM[a[1:0]];

endmodule
