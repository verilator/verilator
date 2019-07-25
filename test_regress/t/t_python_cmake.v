// DESCRIPTION: Verilator: Verilog parameterized test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.
// ======================================================================

// Adds a parameterized constant to an int


module add #( /* verilator lint_off DECLFILENAME */
    parameter integer N = 5
)(
    input wire rst,
    input wire clk,
    input integer value,
    output integer result,
    input wire in1,
    output wire out1,
    input wire[7:0] in8,
    output wire[7:0] out8,
    input wire[15:0] in16,
    output wire[15:0] out16,
    input wire[31:0] in32,
    output wire[31:0] out32,
    input wire[63:0] in64,
    output wire[63:0] out64,
    input wire[127:0] in128,
    output wire[127:0] out128,
    input wire[255:128] in128_2,
    output wire[255:128] out128_2,
    input wire signed in1_s,
    output wire signed out1_s,
    input wire signed [7:0] in8_s,
    output wire signed [7:0] out8_s,
    input wire signed [7:0] in16_s,
    output wire signed [7:0] out16_s,
    input wire signed [7:0] in32_s,
    output wire signed [7:0] out32_s,
    input wire signed [7:0] in64_s,
    output wire signed [7:0] out64_s,
    input wire signed [7:0] in128_s,
    output wire signed [7:0] out128_s
);

always @(posedge clk) begin
    if (rst) begin
        result <= 0;
    end else begin
        result <= value + N;
    end
end

always @(posedge clk) begin
    if (value == 42) begin
        $finish("magic value received");
    end
end

assign out1     = in1;
assign out8     = in8;
assign out16    = in16;
assign out32    = in32;
assign out64    = in64;
assign out128   = in128;
assign out128_2 = in128_2;


assign out1_s = in1_s;
assign out8_s = in8_s;
assign out16_s = in16_s;
assign out32_s = in32_s;
assign out64_s = in64_s;
assign out128_s = in128_s;

endmodule
