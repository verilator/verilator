// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test multiple covergroup instances with separate tracking

module t (/*AUTOARG*/);
    /* verilator lint_off UNSIGNED */
    logic [3:0] data1, data2;

    covergroup cg;
        coverpoint data1 {
            bins low  = {[0:3]};
            bins high = {[4:15]};
        }
    endgroup

    cg cg_inst1, cg_inst2;

    initial begin
        cg_inst1 = new;
        cg_inst2 = new;

        // Initially both have 0% coverage
        check_coverage(cg_inst1, 0.0, "inst1 initial");
        check_coverage(cg_inst2, 0.0, "inst2 initial");

        // Sample different values in each instance
        data1 = 1;
        cg_inst1.sample();  // inst1: low covered (50%)
        check_coverage(cg_inst1, 50.0, "inst1 after low");
        check_coverage(cg_inst2, 0.0, "inst2 still empty");

        data1 = 10;
        cg_inst2.sample();  // inst2: high covered (50%)
        check_coverage(cg_inst1, 50.0, "inst1 still 50%");
        check_coverage(cg_inst2, 50.0, "inst2 after high");

        // Complete coverage in inst1
        data1 = 8;
        cg_inst1.sample();  // inst1: both covered (100%)
        check_coverage(cg_inst1, 100.0, "inst1 complete");
        check_coverage(cg_inst2, 50.0, "inst2 still 50%");

        $write("*-* All Finished *-*\n");
        $finish;
    end

    task check_coverage(cg inst, real expected, string label);
        real cov;
        cov = inst.get_inst_coverage();
        $display("Coverage %s: %0.2f%% (expected ~%0.2f%%)", label, cov, expected);
        if (cov < expected - 0.5 || cov > expected + 0.5) begin
            $error("Coverage mismatch: got %0.2f%%, expected ~%0.2f%%", cov, expected);
            $stop;
        end
    endtask
endmodule
