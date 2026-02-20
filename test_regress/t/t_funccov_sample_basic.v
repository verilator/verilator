// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test basic functional coverage sampling

module t (/*AUTOARG*/);
    /* verilator lint_off UNSIGNED */
    logic [3:0] data;
    int cyc = 0;

    covergroup cg;
        coverpoint data {
            bins low  = {[0:3]};
            bins mid  = {[4:7]};
            bins high = {[8:15]};
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new;

        // Sample different values
        data = 1;  cg_inst.sample();
        data = 5;  cg_inst.sample();
        data = 10; cg_inst.sample();
        data = 2;  cg_inst.sample();  // low hit twice

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
