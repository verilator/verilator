// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test bin options: at_least, weight, goal

module t;
    /* verilator lint_off UNSIGNED */
    bit [7:0] addr;

    covergroup cg;
        option.per_instance = 1;
        option.comment = "Test covergroup with options";

        coverpoint addr {
            option.at_least = 2;  // Each bin needs at least 2 hits
            option.weight = 10;   // This coverpoint has weight 10

            bins low = {[0:3]};
            bins mid = {[4:7]};
            bins high = {[8:15]};
        }
    endgroup

    initial begin
        cg cg_inst;
        real cov;

        cg_inst = new();

        // Hit low once - should be 0% because at_least = 2
        addr = 2;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After 1 hit: %0.2f%%", cov);
        if (cov != 0.0) begin
            $error("Expected 0%% (bin needs 2 hits), got %0.2f%%", cov);
        end

        // Hit low again - should be 33.33% (1/3 bins)
        addr = 1;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After 2 hits to low: %0.2f%%", cov);
        if (cov < 30.0 || cov > 35.0) begin
            $error("Expected ~33.33%%, got %0.2f%%", cov);
        end

        // Hit mid twice - should be 66.67% (2/3 bins)
        addr = 5; cg_inst.sample();
        addr = 6; cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After mid hits: %0.2f%%", cov);
        if (cov < 63.0 || cov > 70.0) begin
            $error("Expected ~66.67%%, got %0.2f%%", cov);
        end

        // Hit high twice - should be 100%
        addr = 10; cg_inst.sample();
        addr = 12; cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        $display("After all bins hit: %0.2f%%", cov);
        if (cov != 100.0) begin
            $error("Expected 100%%, got %0.2f%%", cov);
        end

        $display("Bin options test PASSED");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
