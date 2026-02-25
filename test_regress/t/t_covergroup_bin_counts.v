// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test viewing individual bin hit counts

module t (/*AUTOARG*/);
    /* verilator lint_off UNSIGNED */
    logic [3:0] data;

    covergroup cg;
        coverpoint data {
            bins zero  = {0};
            bins low   = {[1:3]};
            bins mid   = {[4:7]};
            bins high  = {[8:15]};
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new;

        // Sample various values with different frequencies
        data = 0;  cg_inst.sample();  // zero: 1
        data = 1;  cg_inst.sample();  // low: 1
        data = 2;  cg_inst.sample();  // low: 2
        data = 2;  cg_inst.sample();  // low: 3
        data = 5;  cg_inst.sample();  // mid: 1
        data = 10; cg_inst.sample();  // high: 1

        // Verify coverage is 100% (all 4 bins hit)
        check_coverage(100.0, "final");

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
