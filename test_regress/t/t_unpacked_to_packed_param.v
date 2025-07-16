// DESCRIPTION: Verilator: Confirm x randomization stability
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
    // Inputs
    clk
    );

    input clk;

    always @(posedge clk) begin
        $write("*-* All Finished *-*\n");
        $finish;
    end

    localparam logic [1:0][7:0] foo_unpacked [2:0] = '{"12", "34", "56"};
    localparam logic [2:0][1:0][7:0] foo_packed = '{"12", "34", "56"};

    sub #(
        .foos ({foo_unpacked[0], foo_unpacked[1], foo_unpacked[2]})
    ) the_unpacked_sub();

    sub #(
        .foos ({foo_packed[0], foo_packed[1], foo_packed[2]})
    ) the_packed_sub();

endmodule

module sub #(
    parameter logic [2:0][1:0][7:0] foos
);
    initial begin
        if (foos != "563412") $stop;
    end
endmodule
