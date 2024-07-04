// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_emit_accessors(
    input bit in1,
    input bit in2,
    input logic [31:0] in3,
    input logic [31:0] in4,
    output bit out1,
    output logic [31:0] out2,
    output logic [77:0] out3
);
    assign out1 = in1 & in2;
    assign out2 = in3 & in4;
    assign out3 = 1;
endmodule
