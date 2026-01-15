// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();
    reg a;
    wire b;
    initial a = '0;
    assign #1 b = a;

    always @(a, b) begin
        $display("%d a %x, b %x", $time, a, b);
    end

    initial begin
        #5
        if (b != a) $stop;
        #5 a = '1;
        #5
        if (b != a) $stop;
        #5 a = '0;
        #5;
        if (b != a) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
