// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test iff condition filtering in coverpoints

module t (/*AUTOARG*/);
    /* verilator lint_off UNSIGNED */
    logic [3:0] data;
    logic       enable;

    covergroup cg;
        coverpoint data iff (enable) {
            bins low  = {[0:3]};
            bins high = {[4:15]};
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new;

        // Initially no coverage
        check_coverage(0.0, "initial");

        // Sample with enable=0 - should NOT count
        enable = 0;
        data = 1;
        cg_inst.sample();
        check_coverage(0.0, "after sample with enable=0");

        // Sample with enable=1 - should count
        enable = 1;
        data = 1;
        cg_inst.sample();
        check_coverage(50.0, "after sample low with enable=1");

        // Sample high with enable=1
        enable = 1;
        data = 10;
        cg_inst.sample();
        check_coverage(100.0, "after sample high with enable=1");

        // Sample again with enable=0 - should not affect coverage
        enable = 0;
        data = 2;
        cg_inst.sample();
        check_coverage(100.0, "after sample with enable=0 again");

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
