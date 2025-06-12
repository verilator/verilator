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

    big_t bar;
    int cyc;
    real some_real;

    initial begin
        cyc = 0;
        some_real = 5.123;
    end

    always_comb bar = big_t'(some_real);

    always @(posedge clk) begin
        cyc <= cyc + 1;
        some_real <= some_real * 1.234e4;
        if (cyc == 6) begin
            if (foo != 86'd85316302715831280) $stop();
            if (bar != 86'd18089031459271914704338944) $stop();
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end

endmodule
