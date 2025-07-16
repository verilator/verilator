// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
class myClass;
    covergroup embeddedCg;

    endgroup

    function new();
        embeddedCg = new();
        embeddedCg.sample();
        embeddedCg.get_coverage();
    endfunction
endclass

class secondClass;
    covergroup embeddedCg;

    endgroup

    function new();
        embeddedCg = new();
        embeddedCg.sample();
        embeddedCg.get_coverage();
    endfunction
endclass
