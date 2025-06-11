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

    typedef logic [85:0] big_t;
    localparam big_t foo = big_t'(8.531630271583128e+16);

    always @(posedge clk) begin
        if (foo != 86'd85316302715831280) $stop();
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
