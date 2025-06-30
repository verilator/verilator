// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
    covergroup cg_args(int var1, int var2=42);

    endgroup

    cg_args cov1 = new(69, 77);
    cg_args cov2 = new(69);
    function x();
        cov1.sample();
        cov2.get_coverage();
    endfunction;
endmodule
