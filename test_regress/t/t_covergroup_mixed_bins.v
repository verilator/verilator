// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test mixed bin types: single values and ranges

module t (/*AUTOARG*/);
    /* verilator lint_off UNSIGNED */
    logic [7:0] opcode;

    covergroup cg;
        coverpoint opcode {
            bins nop      = {8'h00};
            bins load     = {8'h01, 8'h02, 8'h03};
            bins store    = {8'h04, 8'h05};
            bins arith    = {[8'h10:8'h1F]};
            bins others   = {[8'h20:8'hFE]};  // Avoid 0xFF to prevent CMPCONST warning
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new;

        // Test single value bins
        opcode = 8'h00; cg_inst.sample();  // nop
        check_coverage(20.0, "after nop");

        // Test multi-value list bin
        opcode = 8'h02; cg_inst.sample();  // load
        check_coverage(40.0, "after load");

        opcode = 8'h05; cg_inst.sample();  // store
        check_coverage(60.0, "after store");

        // Test range bin
        opcode = 8'h15; cg_inst.sample();  // arith
        check_coverage(80.0, "after arith");

        opcode = 8'h80; cg_inst.sample();  // others
        check_coverage(100.0, "after others");

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
