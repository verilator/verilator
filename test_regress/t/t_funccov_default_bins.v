// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test default bins - catch-all for values not in other bins

module t;
    /* verilator lint_off UNSIGNED */
    bit [7:0] data;

    covergroup cg;
        coverpoint data {
            bins low = {[0:3]};
            bins high = {[12:15]};
            bins other = default;  // Catches everything else (4-11, 16+)
        }
    endgroup

    initial begin
        cg cg_inst;
        real cov;

        cg_inst = new();

        // Hit low bin
        data = 2;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After low: %0.2f%%", cov);
        if (cov < 30.0 || cov > 35.0) begin
            $error("Expected ~33.33%% (1/3 bins), got %0.2f%%", cov);
        end

        // Hit high bin
        data = 14;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After high: %0.2f%%", cov);
        if (cov < 63.0 || cov > 70.0) begin
            $error("Expected ~66.67%% (2/3 bins), got %0.2f%%", cov);
        end

        // Hit default bin with value 7 (not in low or high)
        data = 7;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After default (7): %0.2f%%", cov);
        if (cov != 100.0) begin
            $error("Expected 100%% (3/3 bins), got %0.2f%%", cov);
        end

        // Hit another default value (should not increase coverage)
        data = 20;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        if (cov != 100.0) begin
            $error("Coverage should stay 100%%, got %0.2f%%", cov);
        end

        $display("Default bins test PASSED");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
