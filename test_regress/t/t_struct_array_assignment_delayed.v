// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by sumpster.
// SPDX-License-Identifier: CC0-1.0

module tb;
    typedef struct {
        logic a;
        logic b;
    } SimpleStruct;

    SimpleStruct s [1];

    logic clock;

    always @(posedge clock) begin
        for (int i = 0; i < 1; i++) begin
            s[i].a <= 1;
            s[i].b <= 0;
        end
    end

    initial begin
        clock = 0;
        s[0].a = 0;
        s[0].b = 0;

        #1 clock = 1;
        #1 if (s[0].a != 1) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
