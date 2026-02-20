// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test 3-way cross coverage

module t;
    /* verilator lint_off UNSIGNED */
    bit [7:0] addr;
    bit [7:0] cmd;
    bit [7:0] data;

    covergroup cg;
        a: coverpoint addr {
            bins low = {[0:1]};
            bins high = {[2:3]};
        }

        b: coverpoint cmd {
            bins read = {0};
            bins write = {1};
        }

        c: coverpoint data {
            bins zero = {0};
            bins one = {1};
        }

        // 3-way cross creates 222 = 8 bins
        abc: cross a, b, c;
    endgroup

    initial begin
        cg cg_inst;
        real cov;
        int expected_bins;

        cg_inst = new();

        // Total bins: 2 (a) + 2 (b) + 2 (c) + 8 (abc) = 14
        expected_bins = 14;

        // Hit: lowreadzero
        addr = 0; cmd = 0; data = 0;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        // Should have: a.low(1), b.read(1), c.zero(1), abc.low_x__read_x__zero(1) = 4/14 = 28.57%
        $display("After sample 1: %0.2f%%", cov);
        if (cov < 25.0 || cov > 32.0) begin
            $error("Expected ~28.57%%, got %0.2f%%", cov);
        end

        // Hit: highwriteone
        addr = 2; cmd = 1; data = 1;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        // Should have 8/14 = 57.14%
        $display("After sample 2: %0.2f%%", cov);
        if (cov < 54.0 || cov > 60.0) begin
            $error("Expected ~57.14%%, got %0.2f%%", cov);
        end

        // Hit remaining 6 cross bins
        addr = 0; cmd = 0; data = 1; cg_inst.sample(); // lowreadone
        addr = 0; cmd = 1; data = 0; cg_inst.sample(); // lowwritezero
        addr = 0; cmd = 1; data = 1; cg_inst.sample(); // lowwriteone
        addr = 2; cmd = 0; data = 0; cg_inst.sample(); // highreadzero
        addr = 2; cmd = 0; data = 1; cg_inst.sample(); // highreadone
        addr = 2; cmd = 1; data = 0; cg_inst.sample(); // highwritezero

        cov = cg_inst.get_inst_coverage();
        $display("After all samples: %0.2f%%", cov);
        if (cov != 100.0) begin
            $error("Expected 100%%, got %0.2f%%", cov);
        end

        $display("3-way cross coverage test PASSED");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
