// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test basic cross coverage functionality

module t;
    /* verilator lint_off UNSIGNED */
    bit [7:0] addr;
    bit [7:0] cmd;

    covergroup cg;
        // Two coverpoints with 2 bins each
        a: coverpoint addr {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }

        b: coverpoint cmd {
            bins read = {0};
            bins write = {1};
        }

        // 2-way cross creates 4 bins: lowread, lowwrite, highread, highwrite
        c: cross a, b;
    endgroup

    initial begin
        cg cg_inst;
        real cov;

        cg_inst = new();

        // Initially coverage should be 0%
        cov = cg_inst.get_inst_coverage();
        if (cov != 0.0) begin
            $error("Initial coverage should be 0%%, got %0.2f%%", cov);
        end

        // Hit lowread
        addr = 2; cmd = 0;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        // Should have: a.low(1), b.read(1), c.low_x__read(1) = 3/8 = 37.5%
        if (cov < 35.0 || cov > 40.0) begin
            $error("After 1 sample, expected ~37.5%%, got %0.2f%%", cov);
        end

        // Hit highwrite
        addr = 5; cmd = 1;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        // Should have: a.low(1), a.high(1), b.read(1), b.write(1),
        //              c.low_x__read(1), c.high_x__write(1) = 6/8 = 75%
        if (cov < 70.0 || cov > 80.0) begin
            $error("After 2 samples, expected ~75%%, got %0.2f%%", cov);
        end

        // Hit lowwrite
        addr = 1; cmd = 1;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        // Should have 7/8 = 87.5%
        if (cov < 85.0 || cov > 90.0) begin
            $error("After 3 samples, expected ~87.5%%, got %0.2f%%", cov);
        end

        // Hit highread for 100% coverage
        addr = 7; cmd = 0;
        cg_inst.sample();
        cov = cg_inst.get_inst_coverage();
        // Should have 8/8 = 100%
        if (cov != 100.0) begin
            $error("After all bins hit, expected 100%%, got %0.2f%%", cov);
        end

        $display("Cross coverage test PASSED - final coverage: %0.2f%%", cov);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
