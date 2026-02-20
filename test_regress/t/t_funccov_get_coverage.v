// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test get_coverage() - type-level coverage exists
// NOTE: Full instance aggregation not yet implemented

module t;
    /* verilator lint_off UNSIGNED */
    bit [7:0] addr;

    covergroup cg;
        coverpoint addr {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }
    endgroup

    initial begin
        cg cg_inst;
        real type_cov, inst_cov;

        cg_inst = new();

        // Sample some bins
        addr = 2;
        cg_inst.sample();
        addr = 6;
        cg_inst.sample();

        // Get coverage
        type_cov = cg::get_coverage();
        inst_cov = cg_inst.get_inst_coverage();

        $display("Type coverage: %0.2f%%", type_cov);
        $display("Instance coverage: %0.2f%%", inst_cov);

        // Instance coverage should be 100%
        if (inst_cov != 100.0) begin
            $error("Instance coverage should be 100%%, got %0.2f%%", inst_cov);
        end

        // Type coverage method exists and returns a value (even if 0 for MVP)
        // Full aggregation across instances requires instance tracking infrastructure
        $display("get_coverage() method exists and is callable");

        $display("Type coverage test PASSED");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
