// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
    // Inputs
    clk
    );
    input clk;

    localparam int width = 8;
    typedef logic [width-1:0] [15:0] two_dee_t;
    typedef logic[$clog2(width)-1:0] index_t;

    two_dee_t the_two_dee;

    initial begin
        the_two_dee[index_t'(5)][7:0] = 8'hab;
        the_two_dee[index_t'(5)][15:8] = 8'h12;
    end

    always @ (posedge clk) begin
        if (the_two_dee[5] != 16'h12ab) $stop();
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
