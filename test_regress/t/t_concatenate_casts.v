// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t;

    typedef logic [7:0] foo_t;
    typedef logic [31:0] bar_t;

    bar_t [1:0] the_bars;

    foo_t [0:0][1:0] the_foos;

    always_comb begin
        the_bars = {32'd7, 32'd8};
        the_foos[0] = {foo_t'(the_bars[1]), foo_t'(the_bars[0])};
        // NOCOMMIT
        // the_foos[0][1] = foo_t'(the_bars[1]);
        // the_foos[0][0] = foo_t'(the_bars[0]);
    end

    initial begin
        // NOCOMMIT -- displays
        $display($bits(the_foos));
        $display($bits(the_foos[0]));
        $display($bits(the_foos[0][0]));
        $display(the_foos[0][1]);
        $display("===> %x", the_foos);
        if (the_foos != 'h0708) $stop();
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
