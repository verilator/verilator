// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
    class base;
        function new();
            g1 = new(0);
        endfunction
        enum {red, green, blue} color;
        covergroup g1 (bit [3:0] a) with function sample(bit b);
            option.weight       = 10;
            option.per_instance = 1;
            coverpoint a;
            coverpoint b;
            c: coverpoint color;
        endgroup
    endclass

    class derived extends base;
        bit d;
        function new();
            super.new();
        endfunction
        covergroup extends g1;
            option.weight = 1;  // overrides the weight from base g1
                                // uses per_instance = 1 from base g1
            c: coverpoint color // overrides the c coverpoint in base g1
            {
                ignore_bins ignore = {blue};
            }
            coverpoint d;       // adds new coverpoint
            cross a, d;         // crosses new coverpoint with inherited one
        endgroup :g1
    endclass
endmodule
