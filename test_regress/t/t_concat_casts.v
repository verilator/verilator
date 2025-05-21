// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package my_pkg;
    typedef enum logic [1:0] {
        SIG_0, SIG_1, SIG_2
    } sig_t;
endpackage : my_pkg


module t;
    import my_pkg::*;

    typedef logic [7:0] foo_t;
    typedef logic [31:0] bar_t;

    bar_t [1:0] the_bars;

    foo_t [0:0][1:0] the_foos;

    always_comb begin
        the_bars = {32'd7, 32'd8};
        the_foos[0] = {foo_t'(the_bars[1]), foo_t'(the_bars[0])};
    end

    logic [6:0] data;
    logic [2:0] opt;

    assign data = 7'b110_0101;
    assign opt = {data[5], sig_t'(data[1:0])};

    initial begin
        if (the_foos != 'h0708) $stop();
        if (opt != 'b101) $stop();
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
