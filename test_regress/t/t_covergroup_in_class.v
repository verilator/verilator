// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
class myClass;
    covergroup embedded_cg;

    endgroup
    
    function new();
        embedded_cg = new();
        embedded_cg.sample();
        embedded_cg.get_coverage();
    endfunction
endclass