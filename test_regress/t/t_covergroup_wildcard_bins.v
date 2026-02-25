// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test wildcard bins with don't care matching

module t;
    /* verilator lint_off UNSIGNED */
    bit [7:0] data;

    covergroup cg;
        coverpoint data {
            // Match any value with upper nibble = 4'b0000
            wildcard bins low = {8'b0000_????};

            // Match any value with upper nibble = 4'b1111
            wildcard bins high = {8'b1111_????};

            // Match specific pattern with don't cares
            wildcard bins pattern = {8'b10?0_11??};
        }
    endgroup

    initial begin
        cg cg_inst;
        real cov;

        cg_inst = new();

        // Test low bin (upper nibble = 0000)
        data = 8'b0000_0101;  // Should match 'low'
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After sample 1 (low): %0.2f%%", cov);
        if (cov < 30.0 || cov > 35.0) begin
            $error("Expected ~33.33%% (1/3 bins), got %0.2f%%", cov);
        end

        // Test high bin (upper nibble = 1111)
        data = 8'b1111_1010;  // Should match 'high'
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After sample 2 (high): %0.2f%%", cov);
        if (cov < 63.0 || cov > 70.0) begin
            $error("Expected ~66.67%% (2/3 bins), got %0.2f%%", cov);
        end

        // Test pattern bin (10?0_11??)
        data = 8'b1000_1101;  // Should match 'pattern' (10[0]0_11[0]1)
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After sample 3 (pattern): %0.2f%%", cov);
        if (cov != 100.0) begin
            $error("Expected 100%% (3/3 bins), got %0.2f%%", cov);
        end

        // Verify another pattern match
        data = 8'b1010_1111;  // Should also match 'pattern' (10[1]0_11[1]1)
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        if (cov != 100.0) begin
            $error("Pattern should still be 100%%, got %0.2f%%", cov);
        end

        // Verify non-matching value doesn't change coverage
        data = 8'b0101_0101;  // Shouldn't match any bin
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        if (cov != 100.0) begin
            $error("Non-matching value shouldn't change coverage, got %0.2f%%", cov);
        end

        $display("Wildcard bins test PASSED - final coverage: %0.2f%%", cov);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
