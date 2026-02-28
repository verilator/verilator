// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test array bins - separate bin per value

module t;
    /* verilator lint_off UNSIGNED */
    bit [7:0] data;

    covergroup cg;
        coverpoint data {
            // Array bins: creates 3 separate bins
            bins values[] = {1, 5, 9};

            // Non-array bin: creates 1 bin covering all values
            bins grouped = {2, 6, 10};
        }
    endgroup

    initial begin
        cg cg_inst;
        real cov;

        cg_inst = new();

        // Initial coverage should be 0%
        cov = cg_inst.get_inst_coverage();
        if (cov != 0.0) begin
            $error("Expected 0%% coverage, got %0.2f%%", cov);
        end

        // Hit first array bin value (1)
        data = 1;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After hitting value 1: %0.2f%%", cov);
        // 1 bin out of 4 total bins (3 array bins + 1 grouped bin)
        if (cov < 23.0 || cov > 27.0) begin
            $error("Expected ~25%% (1/4 bins), got %0.2f%%", cov);
        end

        // Hit second array bin value (5)
        data = 5;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After hitting value 5: %0.2f%%", cov);
        // 2 bins out of 4
        if (cov < 48.0 || cov > 52.0) begin
            $error("Expected ~50%% (2/4 bins), got %0.2f%%", cov);
        end

        // Hit the grouped bin (covers all of 2, 6, 10)
        data = 6;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After hitting grouped bin: %0.2f%%", cov);
        // 3 bins out of 4
        if (cov < 73.0 || cov > 77.0) begin
            $error("Expected ~75%% (3/4 bins), got %0.2f%%", cov);
        end

        // Hit third array bin value (9)
        data = 9;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After hitting value 9: %0.2f%%", cov);
        // All 4 bins covered
        if (cov != 100.0) begin
            $error("Expected 100%% (4/4 bins), got %0.2f%%", cov);
        end

        // Verify hitting other values in grouped bin doesn't increase coverage
        data = 2;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        if (cov != 100.0) begin
            $error("Coverage should stay 100%%, got %0.2f%%", cov);
        end

        $display("Array bins test PASSED");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
