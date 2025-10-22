// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module top_module(
    input   reg     [7:0] in1a,
    input   reg     [7:0] in2a,
    input   reg     [7:0] in1b,
    input   reg     [7:0] in2b,
    output  logic   [7:0] outa,
    output  logic   [7:0] outb
);

    module_a a1 (.in1(in1a), .in2(in2a), .out(outa));
    module_a a2 (.in1(in1b), .in2(in2b), .out(outb));

endmodule

module module_a(
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out
);
    module_b b1 (.in1(in1), .in2(in2), .out(out));
endmodule

module module_b (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out
);
    always_comb begin
        out = in1 + in2;
    end
endmodule
