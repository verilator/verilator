// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module top(input wire clk);

    logic [1:0][31:0] i;
    logic o;

    always @(posedge clk) begin
        force i = 64'hFFFFFFFF_FFFFFFFF;
    end

    sub sub_i(.i(i), .o(o));
endmodule

module sub (
    input  logic [63:0] i,
    output logic o
);
    assign o = |i;
endmodule
