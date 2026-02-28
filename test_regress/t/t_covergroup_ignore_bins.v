// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test ignore_bins - excluded from coverage

module t (/*AUTOARG*/);
    /* verilator lint_off UNSIGNED */
    logic [3:0] data;

    covergroup cg;
        coverpoint data {
            bins low      = {[0:3]};
            bins mid      = {[4:7]};
            bins high     = {[8:11]};
            ignore_bins reserved = {[12:15]};  // Should not count toward coverage
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new;

        // Initially 0% (0 of 3 regular bins)
        check_coverage(0.0, "initial");

        // Hit reserved bin - should still be 0%
        data = 13;
        cg_inst.sample();
        check_coverage(0.0, "after reserved");

        // Hit low bin - now 33.33% (1 of 3)
        data = 1;
        cg_inst.sample();
        check_coverage(33.33, "after low");

        // Hit another reserved value - still 33.33%
        data = 15;
        cg_inst.sample();
        check_coverage(33.33, "after another reserved");

        // Complete regular bins
        data = 5; cg_inst.sample();  // mid
        data = 10; cg_inst.sample(); // high
        check_coverage(100.0, "complete");

        $write("*-* All Finished *-*\n");
        $finish;
    end

    task check_coverage(real expected, string label);
        real cov;
        cov = cg_inst.get_inst_coverage();
        $display("Coverage %s: %0.2f%% (expected ~%0.2f%%)", label, cov, expected);
        if (cov < expected - 0.5 || cov > expected + 0.5) begin
            $error("Coverage mismatch: got %0.2f%%, expected ~%0.2f%%", cov, expected);
            $stop;
        end
    endtask
endmodule
