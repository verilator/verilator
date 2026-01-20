// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();
    // NOCOMMIT -- tests
    // - var initializer
    // - no initializer (possibly while initializing bar to '1)
    // - more than just VarRef in delay assignment
    reg foo;
    wire bar;
    initial foo = '0;
    assign #1 bar = foo;

    always @(foo, bar) begin
        $display("%d foo %x, bar %x", $time, foo, bar);
    end

    initial begin
        #5
        if (bar != foo) $stop;
        #5 foo = '1;
        #5
        if (bar != foo) $stop;
        #5 foo = '0;
        #5;
        if (bar != foo) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
