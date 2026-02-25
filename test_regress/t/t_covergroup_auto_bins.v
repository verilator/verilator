// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
    /* verilator lint_off UNSIGNED */
    /* verilator lint_off CMPCONST */
    logic [2:0] data;  // 3-bit: 0-7

    covergroup cg;
        coverpoint data {
            bins auto[4];  // Should create 4 bins: [0:1], [2:3], [4:5], [6:7]
        }
    endgroup
    /* verilator lint_on CMPCONST */

    initial begin
        automatic cg cg_inst = new;

        // Initial coverage should be 0%
        $display("Coverage initial: %f%% (expected ~0.00%%)", cg_inst.get_inst_coverage());

        // Sample first bin: 0 or 1
        data = 0;
        cg_inst.sample();
        $display("Coverage after 0: %f%% (expected ~25.00%%)", cg_inst.get_inst_coverage());

        // Sample second bin: 2 or 3
        data = 2;
        cg_inst.sample();
        $display("Coverage after 2: %f%% (expected ~50.00%%)", cg_inst.get_inst_coverage());

        // Sample third bin: 4 or 5
        data = 5;
        cg_inst.sample();
        $display("Coverage after 5: %f%% (expected ~75.00%%)", cg_inst.get_inst_coverage());

        // Sample fourth bin: 6 or 7
        data = 7;
        cg_inst.sample();
        $display("Coverage complete: %f%% (expected ~100.00%%)", cg_inst.get_inst_coverage());

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
