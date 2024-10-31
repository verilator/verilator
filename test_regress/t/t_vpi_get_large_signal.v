// DESCRIPTION: Verilator: Demonstrate handling VPI error when trying to fetch
// a large signal's value
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t( /*AUTOARG*/
    clk
);

    input clk;

    // finish report
    always @ (posedge clk) begin
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
