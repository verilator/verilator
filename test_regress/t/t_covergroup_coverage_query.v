// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test querying coverage values via get_inst_coverage

module t (/*AUTOARG*/);
    /* verilator lint_off UNSIGNED */
    logic [3:0] data;

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

        // Initially no coverage
        check_coverage(0.0, "initial");

        // Sample low bin - should be 33.33% (1 of 3 bins)
        data = 1;
        cg_inst.sample();
        check_coverage(33.33, "after low");

        // Sample mid bin - should be 66.67% (2 of 3 bins)
        data = 5;
        cg_inst.sample();
        check_coverage(66.67, "after mid");

        // Sample high bin - should be 100% (3 of 3 bins)
        data = 10;
        cg_inst.sample();
        check_coverage(100.0, "after high");

        // Sample again - coverage should still be 100%
        data = 2;
        cg_inst.sample();
        check_coverage(100.0, "after resample");

        $write("*-* All Finished *-*\n");
        $finish;
    end

    task check_coverage(real expected, string label);
        real cov;
        cov = cg_inst.get_inst_coverage();
        $display("Coverage %s: %0.2f%% (expected ~%0.2f%%)", label, cov, expected);
        // Allow 0.5% tolerance for floating point
        if (cov < expected - 0.5 || cov > expected + 0.5) begin
            $error("Coverage mismatch: got %0.2f%%, expected ~%0.2f%%", cov, expected);
            $stop;
        end
    endtask
endmodule
